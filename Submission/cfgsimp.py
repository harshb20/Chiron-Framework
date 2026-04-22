"""
CFG simplification phase 0.

This pass is detection-only: it rebuilds no IR and performs no CFG or IR
rewrites.  It records conservative simplification opportunities for later
phases.
"""

from dataclasses import dataclass, field

import ChironAST.ChironAST as ChironAST


@dataclass
class CFGSimpInfo:
    unreachable_blocks: set = field(default_factory=set)
    constant_condition_blocks: list = field(default_factory=list)
    nop_only_blocks: set = field(default_factory=set)
    nop_instructions: list = field(default_factory=list)
    jump_only_blocks: set = field(default_factory=set)
    fallthrough_only_blocks: set = field(default_factory=set)
    straight_line_merge_candidates: list = field(default_factory=list)


def _block_key(block):
    if block.name == "START":
        return -1
    if block.name == "END":
        return 10**9
    return block.irID


def _block_names(blocks):
    return [block.name for block in sorted(blocks, key=_block_key)]


def _reachable_blocks(cfg):
    starts = [block for block in cfg.nodes() if block.name == "START"]
    if not starts:
        return set()

    reachable = set()
    worklist = [starts[0]]

    while worklist:
        block = worklist.pop()
        if block in reachable:
            continue
        reachable.add(block)
        worklist.extend(cfg.successors(block))

    return reachable


def _last_instr(block):
    if not block.instrlist:
        return None, None
    return block.instrlist[-1]


def _is_nop_only(block):
    return bool(block.instrlist) and all(
        isinstance(instr, ChironAST.NoOpCommand) for instr, _ in block.instrlist
    )


def _is_control_block(block):
    instr, _ = _last_instr(block)
    return isinstance(instr, ChironAST.ConditionCommand)


def _find_constant_conditions(cfg):
    constants = []
    for block in cfg.nodes():
        instr, ir_idx = _last_instr(block)
        if not isinstance(instr, ChironAST.ConditionCommand):
            continue

        if isinstance(instr.cond, ChironAST.BoolTrue):
            constants.append(
                {
                    "block": block,
                    "ir_idx": ir_idx,
                    "value": True,
                    "kept_edges": [
                        succ
                        for succ in cfg.successors(block)
                        if cfg.get_edge_label(block, succ) == "Cond_True"
                    ],
                    "dead_label": "Cond_False",
                }
            )
        elif isinstance(instr.cond, ChironAST.BoolFalse):
            constants.append(
                {
                    "block": block,
                    "ir_idx": ir_idx,
                    "value": False,
                    "kept_edges": [
                        succ
                        for succ in cfg.successors(block)
                        if cfg.get_edge_label(block, succ) == "Cond_False"
                    ],
                    "dead_label": "Cond_True",
                }
            )

    return constants


def _find_fallthrough_only_blocks(cfg, reachable):
    blocks = set()
    for block in cfg.nodes():
        if block.name in ("START", "END") or block not in reachable:
            continue
        if not _is_nop_only(block):
            continue
        succs = list(cfg.successors(block))
        if len(succs) == 1 and cfg.get_edge_label(block, succs[0]) == "flow_edge":
            blocks.add(block)
    return blocks


def _find_straight_line_merge_candidates(cfg, reachable):
    candidates = []
    for block in cfg.nodes():
        if block.name in ("START", "END") or block not in reachable:
            continue
        if _is_control_block(block):
            continue

        succs = list(cfg.successors(block))
        if len(succs) != 1:
            continue

        succ = succs[0]
        if succ.name == "END" or succ not in reachable:
            continue
        if len(list(cfg.predecessors(succ))) != 1:
            continue

        candidates.append((block, succ))

    candidates.sort(key=lambda pair: (_block_key(pair[0]), _block_key(pair[1])))
    return candidates


def collect_cfg_simplify_info(ir, cfg):
    reachable = _reachable_blocks(cfg)
    blocks = set(cfg.nodes())

    info = CFGSimpInfo()
    info.unreachable_blocks = blocks - reachable
    info.constant_condition_blocks = _find_constant_conditions(cfg)

    for block in cfg.nodes():
        for instr, ir_idx in block.instrlist:
            if isinstance(instr, ChironAST.NoOpCommand):
                info.nop_instructions.append((block, ir_idx))
        if _is_nop_only(block):
            info.nop_only_blocks.add(block)

    info.fallthrough_only_blocks = _find_fallthrough_only_blocks(cfg, reachable)
    info.straight_line_merge_candidates = _find_straight_line_merge_candidates(
        cfg, reachable
    )

    return info


def dump_cfg_simplify_info(info):
    print("\n===== CFG SIMPLIFICATION OPPORTUNITIES =====")
    print(f"  unreachable_blocks={_block_names(info.unreachable_blocks)}")
    print(
        "  constant_condition_blocks="
        + str(
            [
                {
                    "block": item["block"].name,
                    "ir_idx": item["ir_idx"],
                    "value": item["value"],
                    "kept_edges": _block_names(item["kept_edges"]),
                    "dead_label": item["dead_label"],
                }
                for item in info.constant_condition_blocks
            ]
        )
    )
    print(f"  nop_only_blocks={_block_names(info.nop_only_blocks)}")
    print(
        "  nop_instructions="
        + str(
            [
                {"block": block.name, "ir_idx": ir_idx}
                for block, ir_idx in sorted(
                    info.nop_instructions, key=lambda item: item[1]
                )
            ]
        )
    )
    print(f"  jump_only_blocks={_block_names(info.jump_only_blocks)}")
    print(f"  fallthrough_only_blocks={_block_names(info.fallthrough_only_blocks)}")
    print(
        "  straight_line_merge_candidates="
        + str(
            [
                (pred.name, succ.name)
                for pred, succ in info.straight_line_merge_candidates
            ]
        )
    )
    print("============================================\n")


def run_cfg_simplify(ir, cfg, debug=False):
    info = collect_cfg_simplify_info(ir, cfg)
    run_cfg_simplify.last_info = info

    if debug:
        dump_cfg_simplify_info(info)

    return ir


run_cfg_simplify.last_info = CFGSimpInfo()
