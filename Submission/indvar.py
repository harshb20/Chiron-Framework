"""
Phase 1 induction-variable analysis.

This pass detects loop-updated variables and simple basic induction-variable
updates. It intentionally does not rewrite IR.
"""

from collections import defaultdict
from dataclasses import dataclass, field

import ChironAST.ChironAST as ChironAST
from licm import find_loops
from ssa import get_block_instr, get_block_ir_idx


@dataclass(frozen=True)
class LoopUpdate:
    loop_index: int
    header_name: str
    tail_name: str
    block_name: str
    ir_index: int
    varname: str
    instr: object


@dataclass(frozen=True)
class BasicIndVarCandidate:
    loop_index: int
    header_name: str
    tail_name: str
    block_name: str
    ir_index: int
    varname: str
    op: str
    constant: int
    instr: object


@dataclass(frozen=True)
class AmbiguousIndVarSkip:
    loop_index: int
    header_name: str
    tail_name: str
    varname: str
    reason: str
    updates: tuple


@dataclass(frozen=True)
class LoopIndVarInfo:
    loop_index: int
    header_name: str
    tail_name: str
    block_names: tuple
    loop_updated_vars: tuple
    basic_candidates: tuple
    skipped_internal_updates: tuple
    skipped_ambiguous_updates: tuple


@dataclass
class IndVarInfo:
    loops: tuple = field(default_factory=tuple)
    loop_infos: tuple = field(default_factory=tuple)
    loop_updated_vars: tuple = field(default_factory=tuple)
    basic_candidates: tuple = field(default_factory=tuple)
    skipped_internal_updates: tuple = field(default_factory=tuple)
    skipped_ambiguous_updates: tuple = field(default_factory=tuple)


def _block_key(block):
    if block.name == "START":
        return -1
    if block.name == "END":
        return 10**9
    return block.irID


def _block_names(blocks):
    return [block.name for block in sorted(blocks, key=_block_key)]


def _is_internal_loop_var(varname):
    return varname.startswith(":__rep_counter_") or varname.startswith(
        "__rep_counter_"
    )


def _const_value(expr):
    if isinstance(expr, ChironAST.Num):
        return expr.val
    if isinstance(expr, ChironAST.UMinus) and isinstance(expr.expr, ChironAST.Num):
        return -expr.expr.val
    return None


def _is_var(expr, varname):
    return isinstance(expr, ChironAST.Var) and expr.varname == varname


def _match_basic_indvar_update(varname, expr):
    if isinstance(expr, ChironAST.Sum):
        if _is_var(expr.lexpr, varname):
            constant = _const_value(expr.rexpr)
            if constant is not None:
                return "+", constant
        if _is_var(expr.rexpr, varname):
            constant = _const_value(expr.lexpr)
            if constant is not None:
                return "+", constant

    if isinstance(expr, ChironAST.Diff) and _is_var(expr.lexpr, varname):
        constant = _const_value(expr.rexpr)
        if constant is not None:
            return "-", constant

    return None


def _make_basic_candidate(loop_index, loop, update, op, constant):
    return BasicIndVarCandidate(
        loop_index=loop_index,
        header_name=loop.header.name,
        tail_name=loop.tail.name,
        block_name=update.block_name,
        ir_index=update.ir_index,
        varname=update.varname,
        op=op,
        constant=constant,
        instr=update.instr,
    )


def _collect_loop_updates(loop_index, loop):
    updates = []
    skipped_internal = []
    candidates = []
    ambiguous = []
    updates_by_var = defaultdict(list)
    matching_updates_by_var = defaultdict(list)

    for block in sorted(loop.blocks, key=_block_key):
        instr = get_block_instr(block)
        if not isinstance(instr, ChironAST.AssignmentCommand):
            continue

        varname = instr.lvar.varname
        update = LoopUpdate(
            loop_index=loop_index,
            header_name=loop.header.name,
            tail_name=loop.tail.name,
            block_name=block.name,
            ir_index=get_block_ir_idx(block),
            varname=varname,
            instr=instr,
        )

        if _is_internal_loop_var(varname):
            skipped_internal.append(update)
            continue

        updates.append(update)
        updates_by_var[varname].append(update)

        match = _match_basic_indvar_update(varname, instr.rexpr)
        if match is None:
            continue

        matching_updates_by_var[varname].append((update, match[0], match[1]))

    for varname in sorted(matching_updates_by_var):
        matching_updates = matching_updates_by_var[varname]
        var_updates = tuple(updates_by_var[varname])

        if len(matching_updates) != 1 or len(var_updates) != 1:
            ambiguous.append(
                AmbiguousIndVarSkip(
                    loop_index=loop_index,
                    header_name=loop.header.name,
                    tail_name=loop.tail.name,
                    varname=varname,
                    reason=(
                        "multiple loop assignments to same variable"
                        if len(var_updates) != 1
                        else "multiple basic-looking updates to same variable"
                    ),
                    updates=var_updates,
                )
            )
            continue

        update, op, constant = matching_updates[0]
        candidates.append(_make_basic_candidate(loop_index, loop, update, op, constant))

    loop_info = LoopIndVarInfo(
        loop_index=loop_index,
        header_name=loop.header.name,
        tail_name=loop.tail.name,
        block_names=tuple(_block_names(loop.blocks)),
        loop_updated_vars=tuple(updates),
        basic_candidates=tuple(candidates),
        skipped_internal_updates=tuple(skipped_internal),
        skipped_ambiguous_updates=tuple(ambiguous),
    )

    return loop_info


def collect_indvar_info(cfg, ssa_info):
    loops = tuple(find_loops(cfg, ssa_info))
    loop_infos = []
    loop_updated_vars = []
    skipped_internal_updates = []
    skipped_ambiguous_updates = []
    basic_candidates = []

    for loop_index, loop in enumerate(loops):
        loop_info = _collect_loop_updates(loop_index, loop)
        loop_infos.append(loop_info)
        loop_updated_vars.extend(loop_info.loop_updated_vars)
        skipped_internal_updates.extend(loop_info.skipped_internal_updates)
        skipped_ambiguous_updates.extend(loop_info.skipped_ambiguous_updates)
        basic_candidates.extend(loop_info.basic_candidates)

    return IndVarInfo(
        loops=loops,
        loop_infos=tuple(loop_infos),
        loop_updated_vars=tuple(loop_updated_vars),
        basic_candidates=tuple(basic_candidates),
        skipped_internal_updates=tuple(skipped_internal_updates),
        skipped_ambiguous_updates=tuple(skipped_ambiguous_updates),
    )


def _format_updates(updates):
    if not updates:
        return "none"
    return ", ".join(
        f"{update.varname}@ir[{update.ir_index}]" for update in updates
    )


def _format_candidates(candidates):
    if not candidates:
        return "none"
    return ", ".join(
        f"{candidate.varname} {candidate.op} {candidate.constant}@ir[{candidate.ir_index}]"
        for candidate in candidates
    )


def dump_indvar_info(info):
    print("\n===== INDVAR ANALYSIS =====")
    print(f"  loops found: {len(info.loops)}")
    for loop_info in info.loop_infos:
        print(
            "  "
            f"loop {loop_info.loop_index}: "
            f"backedge {loop_info.tail_name} -> {loop_info.header_name}; "
            f"blocks={list(loop_info.block_names)}"
        )
        print(
            "    "
            f"loop-updated vars: {_format_updates(loop_info.loop_updated_vars)}"
        )
        print(
            "    "
            "accepted basic candidates: "
            f"{_format_candidates(loop_info.basic_candidates)}"
        )
        print(
            "    "
            "skipped internal counters: "
            f"{_format_updates(loop_info.skipped_internal_updates)}"
        )
        if loop_info.skipped_ambiguous_updates:
            for skipped in loop_info.skipped_ambiguous_updates:
                print(
                    "    "
                    f"skipped ambiguous {skipped.varname}: "
                    f"{skipped.reason}; updates={_format_updates(skipped.updates)}"
                )

    print(
        "  totals: "
        f"updates={len(info.loop_updated_vars)}, "
        f"basic_candidates={len(info.basic_candidates)}, "
        f"internal_skips={len(info.skipped_internal_updates)}, "
        f"ambiguous_skips={len(info.skipped_ambiguous_updates)}"
    )
    print("===========================\n")


def run_indvar(ir, cfg, ssa_info, debug=False):
    info = collect_indvar_info(cfg, ssa_info)
    run_indvar.last_info = info

    if debug:
        dump_indvar_info(info)

    return ir


run_indvar.last_info = IndVarInfo()
