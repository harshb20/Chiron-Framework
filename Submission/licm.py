"""
Loop Invariant Code Motion (LICM).
"""

import copy
from collections import defaultdict
from dataclasses import dataclass
from typing import Optional

import ChironAST.ChironAST as ChironAST
from ssa import get_block_instr, get_block_ir_idx, vars_in_expr


@dataclass(frozen=True)
class LoopInfo:
    """Natural loop metadata for one backedge."""

    header: object
    tail: object
    blocks: frozenset
    preheader_candidates: frozenset
    dedicated_preheader: Optional[object]
    invariant_candidate_blocks: frozenset


def _block_key(block):
    if block.name == "START":
        return -1
    if block.name == "END":
        return 10**9
    return block.irID


def _block_names(blocks):
    return [b.name for b in sorted(blocks, key=_block_key)]


def _dominates(ssa_info, dominator, block):
    """Return True if dominator dominates block using SSAInfo idom links."""
    if dominator == block:
        return True

    runner = block
    seen = set()
    while runner is not None and runner not in seen:
        seen.add(runner)
        runner = ssa_info.idom.get(runner)
        if runner == dominator:
            return True
    return False


def _natural_loop(cfg, header, tail, reachable_blocks):
    """Collect the natural loop induced by backedge tail -> header."""
    loop_blocks = {header, tail}
    worklist = [tail]

    while worklist:
        block = worklist.pop()
        for pred in cfg.predecessors(block):
            if pred not in reachable_blocks:
                continue
            if pred not in loop_blocks:
                loop_blocks.add(pred)
                worklist.append(pred)

    return loop_blocks


def _contains_div(expr):
    if isinstance(expr, ChironAST.Div):
        return True
    if isinstance(expr, (ChironAST.BinArithOp, ChironAST.BinCondOp)):
        return _contains_div(expr.lexpr) or _contains_div(expr.rexpr)
    if isinstance(expr, (ChironAST.UnaryArithOp, ChironAST.NOT)):
        return _contains_div(expr.expr)
    return False


def _is_rep_counter(varname):
    return varname.startswith(":__rep_counter_") or varname.startswith("__rep_counter_")


def _assignment_candidate_blocks(loop_blocks):
    candidates = []
    for block in loop_blocks:
        instr = get_block_instr(block)
        if not isinstance(instr, ChironAST.AssignmentCommand):
            continue
        if _is_rep_counter(instr.lvar.varname):
            continue
        if _contains_div(instr.rexpr):
            continue
        candidates.append(block)
    return candidates


def _rhs_uses_are_loop_invariant(block, instr, loop_blocks, invariant_blocks, ssa_info):
    for var in vars_in_expr(instr.rexpr):
        ver = ssa_info.var_version_use.get((var, block))
        if ver is None or ver == -1:
            return False

        def_block = ssa_info.def_site.get((var, ver))
        if def_block is None:
            return False
        if def_block not in loop_blocks:
            continue
        if def_block in invariant_blocks:
            continue
        return False
    return True


def find_invariant_candidates(loop_blocks, ssa_info):
    """Find assignment blocks whose RHS is loop-invariant by SSA def-sites."""
    remaining = set(_assignment_candidate_blocks(loop_blocks))
    invariant_blocks = set()

    changed = True
    while changed:
        changed = False
        for block in list(remaining):
            instr = get_block_instr(block)
            if _rhs_uses_are_loop_invariant(
                block, instr, loop_blocks, invariant_blocks, ssa_info
            ):
                remaining.remove(block)
                invariant_blocks.add(block)
                changed = True

    return frozenset(invariant_blocks)


def find_loops(cfg, ssa_info):
    """Detect natural loops from CFG backedges.

    A CFG edge tail -> header is a backedge when header dominates tail.
    For each backedge, build the natural loop block set and record all
    header predecessors outside that loop as preheader candidates.
    """
    reachable_blocks = set(ssa_info.rpo)
    loops = []

    for tail, header in cfg.edges():
        if tail not in reachable_blocks or header not in reachable_blocks:
            continue
        if not _dominates(ssa_info, header, tail):
            continue

        loop_blocks = _natural_loop(cfg, header, tail, reachable_blocks)
        preheader_candidates = {
            pred
            for pred in cfg.predecessors(header)
            if pred in reachable_blocks and pred not in loop_blocks
        }

        dedicated_preheader = None
        if len(preheader_candidates) == 1:
            candidate = next(iter(preheader_candidates))
            candidate_succs = set(cfg.successors(candidate))
            if candidate_succs == {header}:
                dedicated_preheader = candidate

        invariant_candidate_blocks = find_invariant_candidates(loop_blocks, ssa_info)

        loops.append(
            LoopInfo(
                header=header,
                tail=tail,
                blocks=frozenset(loop_blocks),
                preheader_candidates=frozenset(preheader_candidates),
                dedicated_preheader=dedicated_preheader,
                invariant_candidate_blocks=invariant_candidate_blocks,
            )
        )

    loops.sort(key=lambda loop: (_block_key(loop.header), _block_key(loop.tail)))
    return loops


def dump_loops(loops):
    """Print detected LICM loop analysis for debugging."""
    print("\n===== LICM LOOP ANALYSIS =====")
    if not loops:
        print("  No natural loops detected.")
    for loop in loops:
        preheaders = _block_names(loop.preheader_candidates)
        dedicated = loop.dedicated_preheader.name if loop.dedicated_preheader else None
        print(
            "  "
            f"backedge {loop.tail.name} -> {loop.header.name}; "
            f"blocks={_block_names(loop.blocks)}; "
            f"preheader_candidates={preheaders}; "
            f"dedicated_preheader={dedicated}; "
            f"invariant_candidates={_block_names(loop.invariant_candidate_blocks)}"
        )
        for block in sorted(loop.invariant_candidate_blocks, key=_block_key):
            instr = get_block_instr(block)
            print(f"    [{block.name}] ir[{get_block_ir_idx(block)}] {instr}")
    print("==============================\n")


def _is_safe_hoist_assignment(instr):
    if not isinstance(instr, ChironAST.AssignmentCommand):
        return False
    if _is_rep_counter(instr.lvar.varname):
        return False
    if _contains_div(instr.rexpr):
        return False
    return True


def _preheader_insertion_index(ir, loop):
    """Return old IR index where preheader-only hoists should be inserted."""
    preheader = loop.dedicated_preheader
    if preheader is None:
        return None

    preheader_idx = get_block_ir_idx(preheader)
    header_idx = get_block_ir_idx(loop.header)
    if preheader_idx is None or header_idx is None:
        return None
    if preheader_idx < 0 or preheader_idx >= len(ir):
        return None

    preheader_instr, preheader_tgt = ir[preheader_idx]
    if isinstance(preheader_instr, ChironAST.ConditionCommand):
        return None
    if preheader_tgt != 1:
        return None
    if preheader_idx + 1 != header_idx:
        return None

    return header_idx


def _collect_hoists(ir, loops):
    insertions = defaultdict(list)
    replace_with_nop = set()

    for loop in loops:
        insertion_idx = _preheader_insertion_index(ir, loop)
        if insertion_idx is None:
            continue

        for block in sorted(loop.invariant_candidate_blocks, key=_block_key):
            instr = get_block_instr(block)
            old_idx = get_block_ir_idx(block)
            if old_idx is None or old_idx in replace_with_nop:
                continue
            if not _is_safe_hoist_assignment(instr):
                continue

            insertions[insertion_idx].append(copy.deepcopy(instr))
            replace_with_nop.add(old_idx)

    return insertions, replace_with_nop


def _rebuild_ir_with_hoists(ir, insertions, replace_with_nop):
    old_to_new = {}
    rebuilt = []

    for old_idx, (stmt, tgt) in enumerate(ir):
        for hoisted_instr in insertions.get(old_idx, []):
            rebuilt.append((hoisted_instr, None))

        old_to_new[old_idx] = len(rebuilt)
        if old_idx in replace_with_nop:
            rebuilt.append((ChironAST.NoOpCommand(), None))
        else:
            old_target = None
            if isinstance(stmt, ChironAST.ConditionCommand):
                old_target = old_idx + tgt
            rebuilt.append((copy.deepcopy(stmt), old_target))

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


def run_licm(ir, cfg, ssa_info, debug=False):
    """Run conservative LICM and return the rewritten IR."""
    loops = find_loops(cfg, ssa_info)
    run_licm.last_loops = loops
    run_licm.last_invariant_candidates = [
        loop.invariant_candidate_blocks for loop in loops
    ]

    if debug:
        dump_loops(loops)

    insertions, replace_with_nop = _collect_hoists(ir, loops)
    if not replace_with_nop:
        return ir

    return _rebuild_ir_with_hoists(ir, insertions, replace_with_nop)


run_licm.last_loops = []
run_licm.last_invariant_candidates = []
