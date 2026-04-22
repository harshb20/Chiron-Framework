"""
Loop Invariant Code Motion (LICM) scaffolding.

This step is analysis-only: detect natural loops and possible preheader
predecessors, but do not rewrite the IR yet.
"""

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


def run_licm(ir, cfg, ssa_info, debug=False):
    """Run LICM analysis scaffolding and return IR unchanged."""
    loops = find_loops(cfg, ssa_info)
    run_licm.last_loops = loops
    run_licm.last_invariant_candidates = [
        loop.invariant_candidate_blocks for loop in loops
    ]

    if debug:
        dump_loops(loops)

    return ir


run_licm.last_loops = []
run_licm.last_invariant_candidates = []
