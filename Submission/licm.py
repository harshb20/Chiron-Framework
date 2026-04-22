"""
Loop Invariant Code Motion (LICM) scaffolding.

This step is analysis-only: detect natural loops and possible preheader
predecessors, but do not rewrite the IR yet.
"""

from dataclasses import dataclass
from typing import Optional


@dataclass(frozen=True)
class LoopInfo:
    """Natural loop metadata for one backedge."""

    header: object
    tail: object
    blocks: frozenset
    preheader_candidates: frozenset
    dedicated_preheader: Optional[object]


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

        loops.append(
            LoopInfo(
                header=header,
                tail=tail,
                blocks=frozenset(loop_blocks),
                preheader_candidates=frozenset(preheader_candidates),
                dedicated_preheader=dedicated_preheader,
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
            f"dedicated_preheader={dedicated}"
        )
    print("==============================\n")


def run_licm(ir, cfg, ssa_info, debug=False):
    """Run LICM analysis scaffolding and return IR unchanged."""
    loops = find_loops(cfg, ssa_info)
    run_licm.last_loops = loops

    if debug:
        dump_loops(loops)

    return ir


run_licm.last_loops = []
