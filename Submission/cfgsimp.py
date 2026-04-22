"""
CFG simplification.

Phase 0 records conservative simplification opportunities.  Phase 1 performs
literal-constant branch collapse and removes blocks made unreachable by those
collapsed branch choices.  Phase 2 removes reachable NOP-only flow-through
connector blocks.
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


def _constant_condition_taken_label(instr):
    if not isinstance(instr, ChironAST.ConditionCommand):
        return None
    if isinstance(instr.cond, ChironAST.BoolTrue):
        return "Cond_True"
    if isinstance(instr.cond, ChironAST.BoolFalse):
        return "Cond_False"
    return None


def _successors_with_label(cfg, block, label):
    return [
        succ
        for succ in cfg.successors(block)
        if cfg.get_edge_label(block, succ) == label
    ]


def _phase1_successors(cfg, block):
    instr, _ = _last_instr(block)
    taken_label = _constant_condition_taken_label(instr)
    if taken_label is None:
        return list(cfg.successors(block))
    return _successors_with_label(cfg, block, taken_label)


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
        worklist.extend(_phase1_successors(cfg, block))

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


def _first_instr_index(block):
    if block.instrlist:
        return min(ir_idx for _, ir_idx in block.instrlist)
    return _block_key(block)


def _ordered_instr_blocks(blocks):
    return sorted(
        [block for block in blocks if block.instrlist],
        key=_first_instr_index,
    )


def _successor_new_index(successor, block_to_new_start, new_len):
    if successor.name == "END":
        return new_len
    return block_to_new_start.get(successor)


def _effective_successor(cfg, successor, removed_blocks):
    seen = set()
    current = successor

    while current in removed_blocks:
        if current in seen:
            return None
        seen.add(current)

        next_succ = _removed_block_successor(cfg, current)
        if next_succ is None:
            return None
        current = next_succ

    return current


def _removed_block_successor(cfg, block):
    if _is_nop_only(block):
        flow_succs = _successors_with_label(cfg, block, "flow_edge")
        if len(flow_succs) != 1:
            return None
        return flow_succs[0]

    instr, _ = _last_instr(block)
    taken_label = _constant_condition_taken_label(instr)
    if taken_label is None:
        return None

    # A removable constant marker must already have collapsed to one live edge.
    if len(list(cfg.successors(block))) != 1:
        return None

    succs = _successors_with_label(cfg, block, taken_label)
    if len(succs) != 1:
        return None
    return succs[0]


def _effective_successor_new_index(
    cfg, successor, removed_blocks, block_to_new_start, new_len
):
    successor = _effective_successor(cfg, successor, removed_blocks)
    if successor is None:
        return None
    return _successor_new_index(successor, block_to_new_start, new_len)


def _has_phase1_rewrite_opportunity(info, reachable):
    for item in info.constant_condition_blocks:
        if item["block"] in reachable and len(item["kept_edges"]) == 1:
            return True
    return False


def _validate_constant_conditions(info, reachable):
    for item in info.constant_condition_blocks:
        if item["block"] not in reachable:
            continue
        if len(item["kept_edges"]) != 1:
            return False
    return True


def _has_only_local_reachable_predecessors(
    cfg, block, reachable, removed_blocks, order
):
    try:
        block_pos = order.index(block)
    except ValueError:
        return False

    expected_pred = order[block_pos - 1] if block_pos > 0 else None
    for pred in cfg.predecessors(block):
        if pred not in reachable:
            continue
        if pred in removed_blocks:
            return False
        if pred != expected_pred:
            return False

    return True


def _find_redundant_constant_marker_blocks(cfg, reachable, removed_blocks):
    ordered_blocks = _ordered_instr_blocks(set(reachable) - set(removed_blocks))
    redundant = set()

    for idx, block in enumerate(ordered_blocks):
        instr, _ = _last_instr(block)
        if _constant_condition_taken_label(instr) is None:
            continue

        if len(block.instrlist) != 1:
            continue

        successor = _removed_block_successor(cfg, block)
        if successor is None:
            continue

        effective_successor = _effective_successor(cfg, successor, removed_blocks)
        if effective_successor is None:
            continue

        next_block = ordered_blocks[idx + 1] if idx + 1 < len(ordered_blocks) else None
        if next_block is None:
            if effective_successor.name != "END":
                continue
        elif effective_successor != next_block:
            continue

        if not _has_only_local_reachable_predecessors(
            cfg, block, reachable, removed_blocks, ordered_blocks
        ):
            continue

        redundant.add(block)

    return redundant


def _rebuild_ir_cfgsimp(ir, cfg, reachable, info):
    # Phase 2 candidates are the already-detected reachable NOP-only
    # flow-through blocks.  Any ambiguous edge rewrite below aborts the rebuild.
    removed_blocks = set(info.fallthrough_only_blocks)
    constant_marker_blocks = _find_redundant_constant_marker_blocks(
        cfg, reachable, removed_blocks
    )
    removed_blocks.update(constant_marker_blocks)
    has_phase1_rewrite = _has_phase1_rewrite_opportunity(info, reachable)

    if not has_phase1_rewrite and not removed_blocks:
        return ir
    if not _validate_constant_conditions(info, reachable):
        return ir

    kept_blocks = set(reachable) - removed_blocks
    ordered_blocks = _ordered_instr_blocks(kept_blocks)
    kept = []
    block_to_new_start = {}
    block_to_new_end = {}

    for block in ordered_blocks:
        instrs = sorted(block.instrlist, key=lambda item: item[1])
        block_to_new_start[block] = len(kept)
        for instr, _ in instrs:
            kept.append((block, instr))
        block_to_new_end[block] = len(kept) - 1

    new_len = len(kept)
    new_ir = []

    for new_idx, (block, instr) in enumerate(kept):
        is_block_end = new_idx == block_to_new_end[block]

        if isinstance(instr, ChironAST.ConditionCommand):
            if not is_block_end:
                return ir

            if isinstance(instr.cond, ChironAST.BoolTrue):
                true_succs = _successors_with_label(cfg, block, "Cond_True")
                if len(true_succs) != 1:
                    return ir

                true_idx = _effective_successor_new_index(
                    cfg, true_succs[0], removed_blocks, block_to_new_start, new_len
                )
                if true_idx is None or true_idx != new_idx + 1:
                    return ir

                new_ir.append((instr, 1))
                continue

            false_succs = _successors_with_label(cfg, block, "Cond_False")
            if len(false_succs) != 1:
                return ir

            false_idx = _effective_successor_new_index(
                cfg, false_succs[0], removed_blocks, block_to_new_start, new_len
            )
            if false_idx is None:
                return ir

            if not isinstance(instr.cond, ChironAST.BoolFalse):
                true_succs = _successors_with_label(cfg, block, "Cond_True")
                if len(true_succs) != 1:
                    return ir

                true_idx = _effective_successor_new_index(
                    cfg, true_succs[0], removed_blocks, block_to_new_start, new_len
                )
                if true_idx is None or true_idx != new_idx + 1:
                    return ir

            new_ir.append((instr, false_idx - new_idx))
            continue

        if is_block_end:
            flow_succs = _successors_with_label(cfg, block, "flow_edge")
            if len(flow_succs) != 1:
                return ir

            flow_idx = _effective_successor_new_index(
                cfg, flow_succs[0], removed_blocks, block_to_new_start, new_len
            )
            if flow_idx is None or flow_idx != new_idx + 1:
                return ir

        new_ir.append((instr, 1))

    return new_ir


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

    reachable = set(cfg.nodes()) - info.unreachable_blocks
    return _rebuild_ir_cfgsimp(ir, cfg, reachable, info)


run_cfg_simplify.last_info = CFGSimpInfo()
