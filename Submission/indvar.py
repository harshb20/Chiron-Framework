"""
Phase 1/2 induction-variable analysis plus a conservative Phase 3 rewrite.

This pass detects loop-updated variables and simple basic induction-variable
updates, records simple derived induction-variable candidates, and performs a
small strength-reduction rewrite when the loop shape is unambiguous.
"""

import copy
from collections import defaultdict
from dataclasses import dataclass, field

import ChironAST.ChironAST as ChironAST
from licm import find_loops
from ssa import get_block_instr, get_block_ir_idx, vars_in_expr, vars_used_in


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
class DerivedIndVarCandidate:
    loop_index: int
    header_name: str
    tail_name: str
    block_name: str
    ir_index: int
    varname: str
    base_varname: str
    op: str
    form: str
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
class AmbiguousDerivedIndVarSkip:
    loop_index: int
    header_name: str
    tail_name: str
    block_name: str
    ir_index: int
    varname: str
    reason: str
    updates: tuple
    instr: object


@dataclass(frozen=True)
class LoopIndVarInfo:
    loop_index: int
    header_name: str
    tail_name: str
    block_names: tuple
    loop_updated_vars: tuple
    basic_candidates: tuple
    derived_candidates: tuple
    skipped_internal_updates: tuple
    skipped_ambiguous_updates: tuple
    skipped_ambiguous_derived: tuple


@dataclass
class IndVarInfo:
    loops: tuple = field(default_factory=tuple)
    loop_infos: tuple = field(default_factory=tuple)
    loop_updated_vars: tuple = field(default_factory=tuple)
    basic_candidates: tuple = field(default_factory=tuple)
    derived_candidates: tuple = field(default_factory=tuple)
    skipped_internal_updates: tuple = field(default_factory=tuple)
    skipped_ambiguous_updates: tuple = field(default_factory=tuple)
    skipped_ambiguous_derived: tuple = field(default_factory=tuple)


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


def _accepted_basic_var(expr, basic_varnames):
    if isinstance(expr, ChironAST.Var) and expr.varname in basic_varnames:
        return expr.varname
    return None


def _contains_div(expr):
    if isinstance(expr, ChironAST.Div):
        return True
    if isinstance(expr, (ChironAST.BinArithOp, ChironAST.BinCondOp)):
        return _contains_div(expr.lexpr) or _contains_div(expr.rexpr)
    if isinstance(expr, (ChironAST.UnaryArithOp, ChironAST.NOT)):
        return _contains_div(expr.expr)
    return False


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


def _match_derived_indvar_update(expr, basic_varnames):
    if isinstance(expr, ChironAST.Mult):
        base_varname = _accepted_basic_var(expr.lexpr, basic_varnames)
        constant = _const_value(expr.rexpr)
        if base_varname is not None and constant is not None:
            return base_varname, "*", "base * constant", constant

        base_varname = _accepted_basic_var(expr.rexpr, basic_varnames)
        constant = _const_value(expr.lexpr)
        if base_varname is not None and constant is not None:
            return base_varname, "*", "constant * base", constant

    if isinstance(expr, ChironAST.Sum):
        base_varname = _accepted_basic_var(expr.lexpr, basic_varnames)
        constant = _const_value(expr.rexpr)
        if base_varname is not None and constant is not None:
            return base_varname, "+", "base + constant", constant

        base_varname = _accepted_basic_var(expr.rexpr, basic_varnames)
        constant = _const_value(expr.lexpr)
        if base_varname is not None and constant is not None:
            return base_varname, "+", "constant + base", constant

    if isinstance(expr, ChironAST.Diff):
        base_varname = _accepted_basic_var(expr.lexpr, basic_varnames)
        constant = _const_value(expr.rexpr)
        if base_varname is not None and constant is not None:
            return base_varname, "-", "base - constant", constant

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


def _make_derived_candidate(loop_index, loop, update, match):
    base_varname, op, form, constant = match
    return DerivedIndVarCandidate(
        loop_index=loop_index,
        header_name=loop.header.name,
        tail_name=loop.tail.name,
        block_name=update.block_name,
        ir_index=update.ir_index,
        varname=update.varname,
        base_varname=base_varname,
        op=op,
        form=form,
        constant=constant,
        instr=update.instr,
    )


def _derived_skip_reason(expr, basic_varnames, loop_updated_varnames):
    expr_vars = vars_in_expr(expr)
    if not (expr_vars & basic_varnames):
        return None

    if _contains_div(expr):
        return "division expression"

    changing_vars = expr_vars & loop_updated_varnames
    if len(changing_vars) > 1:
        return "multiple changing variables in expression"

    if isinstance(expr, ChironAST.BinArithOp):
        return "nonlinear or unsupported derived expression"

    return None


def _add_derived_skip(skipped, seen_skips, loop_index, loop, update, reason, updates):
    key = (update.varname, reason)
    if key in seen_skips:
        return
    seen_skips.add(key)
    skipped.append(
        AmbiguousDerivedIndVarSkip(
            loop_index=loop_index,
            header_name=loop.header.name,
            tail_name=loop.tail.name,
            block_name=update.block_name,
            ir_index=update.ir_index,
            varname=update.varname,
            reason=reason,
            updates=tuple(updates),
            instr=update.instr,
        )
    )


def _collect_derived_candidates(loop_index, loop, updates, updates_by_var, basic_candidates):
    basic_varnames = {candidate.varname for candidate in basic_candidates}
    if not basic_varnames:
        return (), ()

    loop_updated_varnames = set(updates_by_var)
    derived = []
    skipped = []
    seen_skips = set()

    for update in updates:
        if update.varname in basic_varnames:
            continue

        expr = update.instr.rexpr
        match = _match_derived_indvar_update(expr, basic_varnames)
        dest_updates = updates_by_var[update.varname]

        if match is not None:
            if len(dest_updates) != 1:
                _add_derived_skip(
                    skipped,
                    seen_skips,
                    loop_index,
                    loop,
                    update,
                    "multiple loop assignments to same destination variable",
                    dest_updates,
                )
                continue
            derived.append(_make_derived_candidate(loop_index, loop, update, match))
            continue

        reason = _derived_skip_reason(expr, basic_varnames, loop_updated_varnames)
        if reason is None:
            continue
        if len(dest_updates) != 1:
            reason = "multiple loop assignments to same destination variable"
        _add_derived_skip(
            skipped, seen_skips, loop_index, loop, update, reason, dest_updates
        )

    return tuple(derived), tuple(skipped)


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

    derived_candidates, ambiguous_derived = _collect_derived_candidates(
        loop_index, loop, updates, updates_by_var, candidates
    )

    loop_info = LoopIndVarInfo(
        loop_index=loop_index,
        header_name=loop.header.name,
        tail_name=loop.tail.name,
        block_names=tuple(_block_names(loop.blocks)),
        loop_updated_vars=tuple(updates),
        basic_candidates=tuple(candidates),
        derived_candidates=derived_candidates,
        skipped_internal_updates=tuple(skipped_internal),
        skipped_ambiguous_updates=tuple(ambiguous),
        skipped_ambiguous_derived=ambiguous_derived,
    )

    return loop_info


def collect_indvar_info(cfg, ssa_info):
    loops = tuple(find_loops(cfg, ssa_info))
    loop_infos = []
    loop_updated_vars = []
    skipped_internal_updates = []
    skipped_ambiguous_updates = []
    skipped_ambiguous_derived = []
    basic_candidates = []
    derived_candidates = []

    for loop_index, loop in enumerate(loops):
        loop_info = _collect_loop_updates(loop_index, loop)
        loop_infos.append(loop_info)
        loop_updated_vars.extend(loop_info.loop_updated_vars)
        skipped_internal_updates.extend(loop_info.skipped_internal_updates)
        skipped_ambiguous_updates.extend(loop_info.skipped_ambiguous_updates)
        skipped_ambiguous_derived.extend(loop_info.skipped_ambiguous_derived)
        basic_candidates.extend(loop_info.basic_candidates)
        derived_candidates.extend(loop_info.derived_candidates)

    return IndVarInfo(
        loops=loops,
        loop_infos=tuple(loop_infos),
        loop_updated_vars=tuple(loop_updated_vars),
        basic_candidates=tuple(basic_candidates),
        derived_candidates=tuple(derived_candidates),
        skipped_internal_updates=tuple(skipped_internal_updates),
        skipped_ambiguous_updates=tuple(skipped_ambiguous_updates),
        skipped_ambiguous_derived=tuple(skipped_ambiguous_derived),
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


def _format_derived_candidates(candidates):
    if not candidates:
        return "none"
    formatted = []
    for candidate in candidates:
        rhs = candidate.form.replace("base", candidate.base_varname).replace(
            "constant", str(candidate.constant)
        )
        formatted.append(f"{candidate.varname} = {rhs}@ir[{candidate.ir_index}]")
    return ", ".join(formatted)


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
            "accepted basic induction vars: "
            f"{_format_candidates(loop_info.basic_candidates)}"
        )
        print(
            "    "
            "accepted derived induction vars: "
            f"{_format_derived_candidates(loop_info.derived_candidates)}"
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
        if loop_info.skipped_ambiguous_derived:
            for skipped in loop_info.skipped_ambiguous_derived:
                print(
                    "    "
                    f"skipped ambiguous derived {skipped.varname}: "
                    f"{skipped.reason}; updates={_format_updates(skipped.updates)}"
                )

    print(
        "  totals: "
        f"updates={len(info.loop_updated_vars)}, "
        f"basic_candidates={len(info.basic_candidates)}, "
        f"derived_candidates={len(info.derived_candidates)}, "
        f"internal_skips={len(info.skipped_internal_updates)}, "
        f"ambiguous_skips={len(info.skipped_ambiguous_updates)}, "
        f"ambiguous_derived_skips={len(info.skipped_ambiguous_derived)}"
    )
    print("===========================\n")


def _instr_contains_div(instr):
    if isinstance(instr, ChironAST.AssignmentCommand):
        return _contains_div(instr.rexpr)
    if isinstance(instr, ChironAST.ConditionCommand):
        return _contains_div(instr.cond)
    if isinstance(instr, ChironAST.AssertCommand):
        return _contains_div(instr.cond)
    if isinstance(instr, ChironAST.MoveCommand):
        return _contains_div(instr.expr)
    if isinstance(instr, ChironAST.GotoCommand):
        return _contains_div(instr.xcor) or _contains_div(instr.ycor)
    return False


def _condition_old_target(ir, old_idx):
    stmt, tgt = ir[old_idx]
    if isinstance(stmt, ChironAST.ConditionCommand):
        return old_idx + tgt
    return None


def _preheader_insertion_index(ir, loop):
    preheader = loop.dedicated_preheader
    if preheader is None:
        return None

    preheader_idx = get_block_ir_idx(preheader)
    header_idx = get_block_ir_idx(loop.header)
    if preheader_idx is None or header_idx is None:
        return None
    if preheader_idx < 0 or preheader_idx >= len(ir):
        return None
    if preheader_idx + 1 != header_idx:
        return None

    preheader_instr, preheader_tgt = ir[preheader_idx]
    if isinstance(preheader_instr, ChironAST.ConditionCommand):
        return None
    if preheader_tgt != 1:
        return None

    return header_idx


def _match_positive_repeat_header(instr):
    if not isinstance(instr, ChironAST.ConditionCommand):
        return None

    cond = instr.cond
    if not isinstance(cond, ChironAST.GT):
        return None
    if not isinstance(cond.lexpr, ChironAST.Var):
        return None
    if _const_value(cond.rexpr) != 0:
        return None

    varname = cond.lexpr.varname
    if not _is_internal_loop_var(varname):
        return None
    return varname


def _has_positive_repeat_count(ir, loop, counter_varname):
    preheader = loop.dedicated_preheader
    if preheader is None:
        return False

    preheader_idx = get_block_ir_idx(preheader)
    if preheader_idx is None or preheader_idx < 0 or preheader_idx >= len(ir):
        return False

    instr, _ = ir[preheader_idx]
    if not isinstance(instr, ChironAST.AssignmentCommand):
        return False
    if instr.lvar.varname != counter_varname:
        return False

    repeat_count = _const_value(instr.rexpr)
    return repeat_count is not None and repeat_count > 0


def _is_standard_counter_decrement(update, counter_varname):
    if update.varname != counter_varname:
        return False
    match = _match_basic_indvar_update(counter_varname, update.instr.rexpr)
    return match == ("-", 1)


def _simple_repeat_loop_shape(ir, loop_info, loop):
    header_idx = get_block_ir_idx(loop.header)
    tail_idx = get_block_ir_idx(loop.tail)
    if header_idx is None or tail_idx is None:
        return None
    if not (0 <= header_idx < tail_idx < len(ir)):
        return None

    loop_indices = sorted(
        get_block_ir_idx(block)
        for block in loop.blocks
        if get_block_ir_idx(block) is not None
    )
    if loop_indices != list(range(header_idx, tail_idx + 1)):
        return None

    header_instr, _ = ir[header_idx]
    counter_varname = _match_positive_repeat_header(header_instr)
    if counter_varname is None:
        return None
    if not _has_positive_repeat_count(ir, loop, counter_varname):
        return None

    tail_instr, _ = ir[tail_idx]
    if not isinstance(tail_instr, ChironAST.ConditionCommand):
        return None
    if not isinstance(tail_instr.cond, ChironAST.BoolFalse):
        return None
    if _condition_old_target(ir, tail_idx) != header_idx:
        return None

    header_exit_idx = _condition_old_target(ir, header_idx)
    if header_exit_idx != tail_idx + 1:
        return None

    if _preheader_insertion_index(ir, loop) != header_idx:
        return None

    internal_updates = [
        update
        for update in loop_info.skipped_internal_updates
        if _is_internal_loop_var(update.varname)
    ]
    if len(internal_updates) != 1:
        return None
    if not _is_standard_counter_decrement(internal_updates[0], counter_varname):
        return None

    for block in loop.blocks:
        idx = get_block_ir_idx(block)
        instr = get_block_instr(block)
        if idx is None or instr is None:
            return None
        if _instr_contains_div(instr):
            return None
        if isinstance(instr, ChironAST.ConditionCommand) and idx not in (
            header_idx,
            tail_idx,
        ):
            return None
        for varname in vars_used_in(instr):
            if _is_internal_loop_var(varname) and varname != counter_varname:
                return None

    return header_idx, tail_idx


def _assignment_counts_by_var(loop):
    counts = defaultdict(int)
    for block in loop.blocks:
        instr = get_block_instr(block)
        if isinstance(instr, ChironAST.AssignmentCommand):
            counts[instr.lvar.varname] += 1
    return counts


def _uses_var(instr, varname):
    return varname in vars_used_in(instr)


def _derived_uses_allow_post_basic_update(ir, loop, basic, derived):
    tail_idx = get_block_ir_idx(loop.tail)
    if tail_idx is None:
        return False

    for block in loop.blocks:
        idx = get_block_ir_idx(block)
        if idx is None or idx == derived.ir_index:
            continue
        instr = get_block_instr(block)
        if instr is None or not _uses_var(instr, derived.varname):
            continue
        if not (derived.ir_index < idx < basic.ir_index):
            return False

    for idx in range(tail_idx + 1, len(ir)):
        if _uses_var(ir[idx][0], derived.varname):
            return False

    return True


def _make_increment_expr(varname, step):
    if step >= 0:
        return ChironAST.Sum(ChironAST.Var(varname), ChironAST.Num(step))
    return ChironAST.Diff(ChironAST.Var(varname), ChironAST.Num(-step))


def _phase3_rewrite_for_loop(ir, loop_info, loop):
    if len(loop_info.basic_candidates) != 1:
        return None
    if len(loop_info.derived_candidates) != 1:
        return None
    if loop_info.skipped_ambiguous_updates or loop_info.skipped_ambiguous_derived:
        return None

    basic = loop_info.basic_candidates[0]
    derived = loop_info.derived_candidates[0]

    if _is_internal_loop_var(basic.varname) or _is_internal_loop_var(derived.varname):
        return None
    if derived.base_varname != basic.varname:
        return None
    if derived.op != "*":
        return None

    loop_bounds = _simple_repeat_loop_shape(ir, loop_info, loop)
    if loop_bounds is None:
        return None
    header_idx, tail_idx = loop_bounds

    if not (header_idx < derived.ir_index < basic.ir_index < tail_idx):
        return None

    assignment_counts = _assignment_counts_by_var(loop)
    if assignment_counts[derived.varname] != 1:
        return None
    if assignment_counts[basic.varname] != 1:
        return None

    if not _derived_uses_allow_post_basic_update(ir, loop, basic, derived):
        return None

    basic_delta = basic.constant if basic.op == "+" else -basic.constant
    derived_delta = basic_delta * derived.constant
    if derived_delta == 0:
        return None

    init_instr = ChironAST.AssignmentCommand(
        copy.deepcopy(derived.instr.lvar),
        copy.deepcopy(derived.instr.rexpr),
    )
    update_instr = ChironAST.AssignmentCommand(
        ChironAST.Var(derived.varname),
        _make_increment_expr(derived.varname, derived_delta),
    )

    return {
        "insert_before": {header_idx: [init_instr]},
        "insert_after": {basic.ir_index: [update_instr]},
        "replace_with_nop": {derived.ir_index},
    }


def _rebuild_ir_with_indvar_rewrites(
    ir, insert_before, insert_after, replace_with_nop
):
    old_to_new = {}
    rebuilt = []

    for old_idx, (stmt, tgt) in enumerate(ir):
        for inserted in insert_before.get(old_idx, []):
            rebuilt.append((inserted, None))

        old_to_new[old_idx] = len(rebuilt)
        if old_idx in replace_with_nop:
            rebuilt.append((ChironAST.NoOpCommand(), None))
        else:
            old_target = None
            if isinstance(stmt, ChironAST.ConditionCommand):
                old_target = old_idx + tgt
            rebuilt.append((copy.deepcopy(stmt), old_target))

        for inserted in insert_after.get(old_idx, []):
            rebuilt.append((inserted, None))

    old_to_new[len(ir)] = len(rebuilt)

    new_ir = []
    for new_idx, (stmt, old_target) in enumerate(rebuilt):
        if isinstance(stmt, ChironAST.ConditionCommand):
            if old_target is None:
                new_tgt = 1
            else:
                old_target = max(0, min(old_target, len(ir)))
                new_tgt = old_to_new[old_target] - new_idx
            new_ir.append((stmt, new_tgt))
        else:
            new_ir.append((stmt, 1))

    return new_ir


def _apply_phase3_strength_reduction(ir, info):
    rewrite_plan = None

    for loop_info, loop in zip(info.loop_infos, info.loops):
        plan = _phase3_rewrite_for_loop(ir, loop_info, loop)
        if plan is not None:
            if rewrite_plan is not None:
                return ir
            rewrite_plan = plan

    if rewrite_plan is None:
        return ir

    return _rebuild_ir_with_indvar_rewrites(
        ir,
        rewrite_plan["insert_before"],
        rewrite_plan["insert_after"],
        rewrite_plan["replace_with_nop"],
    )


def run_indvar(ir, cfg, ssa_info, debug=False):
    info = collect_indvar_info(cfg, ssa_info)
    run_indvar.last_info = info

    if debug:
        dump_indvar_info(info)

    return _apply_phase3_strength_reduction(ir, info)


run_indvar.last_info = IndVarInfo()
