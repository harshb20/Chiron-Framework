"""
Phase 0 induction-variable analysis.

This pass detects loop-updated variables and simple basic induction-variable
updates. It intentionally does not rewrite IR.
"""

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


@dataclass
class IndVarInfo:
    loops: tuple = field(default_factory=tuple)
    loop_updated_vars: tuple = field(default_factory=tuple)
    basic_candidates: tuple = field(default_factory=tuple)
    skipped_internal_updates: tuple = field(default_factory=tuple)


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


def _collect_loop_updates(loop_index, loop):
    updates = []
    skipped_internal = []
    candidates = []

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

        match = _match_basic_indvar_update(varname, instr.rexpr)
        if match is None:
            continue

        op, constant = match
        candidates.append(
            BasicIndVarCandidate(
                loop_index=loop_index,
                header_name=loop.header.name,
                tail_name=loop.tail.name,
                block_name=block.name,
                ir_index=get_block_ir_idx(block),
                varname=varname,
                op=op,
                constant=constant,
                instr=instr,
            )
        )

    return updates, skipped_internal, candidates


def collect_indvar_info(cfg, ssa_info):
    loops = tuple(find_loops(cfg, ssa_info))
    loop_updated_vars = []
    skipped_internal_updates = []
    basic_candidates = []

    for loop_index, loop in enumerate(loops):
        updates, skipped_internal, candidates = _collect_loop_updates(
            loop_index, loop
        )
        loop_updated_vars.extend(updates)
        skipped_internal_updates.extend(skipped_internal)
        basic_candidates.extend(candidates)

    return IndVarInfo(
        loops=loops,
        loop_updated_vars=tuple(loop_updated_vars),
        basic_candidates=tuple(basic_candidates),
        skipped_internal_updates=tuple(skipped_internal_updates),
    )


def dump_indvar_info(info):
    print("\n===== INDVAR ANALYSIS =====")
    print(f"  loops found: {len(info.loops)}")
    for idx, loop in enumerate(info.loops):
        print(
            "  "
            f"loop {idx}: backedge {loop.tail.name} -> {loop.header.name}; "
            f"blocks={_block_names(loop.blocks)}"
        )

    print(f"  loop-updated variables: {len(info.loop_updated_vars)}")
    for update in info.loop_updated_vars:
        print(
            "    "
            f"loop {update.loop_index} [{update.block_name}] "
            f"ir[{update.ir_index}] {update.instr}"
        )

    print(f"  candidate basic induction variable updates: {len(info.basic_candidates)}")
    for candidate in info.basic_candidates:
        print(
            "    "
            f"loop {candidate.loop_index} [{candidate.block_name}] "
            f"ir[{candidate.ir_index}] {candidate.varname} = "
            f"{candidate.varname} {candidate.op} {candidate.constant}"
        )

    print(f"  skipped internal loop-counter updates: {len(info.skipped_internal_updates)}")
    for update in info.skipped_internal_updates:
        print(
            "    "
            f"loop {update.loop_index} [{update.block_name}] "
            f"ir[{update.ir_index}] {update.instr}"
        )
    print("===========================\n")


def run_indvar(ir, cfg, ssa_info, debug=False):
    info = collect_indvar_info(cfg, ssa_info)
    run_indvar.last_info = info

    if debug:
        dump_indvar_info(info)

    return ir


run_indvar.last_info = IndVarInfo()
