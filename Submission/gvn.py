"""
Phase 0 Global Value Numbering / Common Subexpression Elimination.

This pass currently performs detection only. It records conservative local
common-subexpression candidates over straight-line CFG regions and leaves the
IR unchanged.
"""

from collections import defaultdict
from dataclasses import dataclass, field

import ChironAST.ChironAST as ChironAST
from ssa import get_block_instr, get_block_ir_idx


@dataclass(frozen=True)
class CSEOccurrence:
    region_id: int
    block_name: str
    ir_index: int
    target: str
    expression: str
    instr: object


@dataclass(frozen=True)
class CSECandidate:
    region_id: int
    expression_key: tuple
    op: str
    expression: str
    occurrences: tuple


@dataclass(frozen=True)
class GVNSkip:
    region_id: int
    block_name: str
    ir_index: int
    reason: str
    detail: str


@dataclass
class GVNInfo:
    regions: tuple = field(default_factory=tuple)
    candidates: tuple = field(default_factory=tuple)
    skipped: tuple = field(default_factory=tuple)


_BINOP_INFO = (
    (ChironAST.Sum, "+", True),
    (ChironAST.Diff, "-", False),
    (ChironAST.Mult, "*", True),
)


def _block_key(block):
    if block.name == "START":
        return -1
    if block.name == "END":
        return 10**9

    ir_idx = get_block_ir_idx(block)
    if ir_idx is not None:
        return ir_idx
    return block.irID


def _contains_div(expr):
    if isinstance(expr, ChironAST.Div):
        return True
    if isinstance(expr, (ChironAST.BinArithOp, ChironAST.BinCondOp)):
        return _contains_div(expr.lexpr) or _contains_div(expr.rexpr)
    if isinstance(expr, (ChironAST.UnaryArithOp, ChironAST.NOT)):
        return _contains_div(expr.expr)
    return False


def _operand_key(expr, block, ssa_info):
    if isinstance(expr, ChironAST.Num):
        return ("num", expr.val), frozenset()

    if isinstance(expr, ChironAST.Var):
        version = ssa_info.var_version_use.get((expr.varname, block))
        if version is None:
            return None, frozenset()
        return ("var", expr.varname, version), frozenset({expr.varname})

    return None, frozenset()


def _expr_key(expr, block, ssa_info):
    if _contains_div(expr):
        return None, None, frozenset(), "contains Div"

    for cls, op, commutative in _BINOP_INFO:
        if not isinstance(expr, cls):
            continue

        left_key, left_vars = _operand_key(expr.lexpr, block, ssa_info)
        right_key, right_vars = _operand_key(expr.rexpr, block, ssa_info)
        if left_key is None or right_key is None:
            return None, op, frozenset(), "unsupported operand"

        operands = (left_key, right_key)
        if commutative:
            operands = tuple(sorted(operands, key=repr))

        key = (op,) + operands
        return key, op, left_vars | right_vars, None

    return None, None, frozenset(), "unsupported RHS"


def _single_flow_successor(cfg, block, reachable):
    succs = [succ for succ in cfg.successors(block) if succ in reachable]
    if len(succs) != 1:
        return None

    succ = succs[0]
    if succ.name == "END":
        return None
    if cfg.get_edge_label(block, succ) != "flow_edge":
        return None

    preds = [pred for pred in cfg.predecessors(succ) if pred in reachable]
    if len(preds) != 1:
        return None

    return succ


def _straight_line_regions(cfg, ssa_info):
    reachable = set(ssa_info.rpo)
    blocks = [
        block
        for block in sorted(reachable, key=_block_key)
        if get_block_instr(block) is not None
    ]

    regions = []
    visited = set()

    for block in blocks:
        if block in visited:
            continue

        region = []
        current = block
        while current not in visited and get_block_instr(current) is not None:
            region.append(current)
            visited.add(current)

            succ = _single_flow_successor(cfg, current, reachable)
            if succ is None or succ in visited:
                break
            current = succ

        if region:
            regions.append(tuple(region))

    return tuple(regions)


def collect_gvn_info(ir, cfg, ssa_info):
    regions = _straight_line_regions(cfg, ssa_info)
    skipped = []
    groups = {}
    active = {}
    next_group_id = 0

    for region_id, region in enumerate(regions):
        active.clear()

        for block in region:
            instr = get_block_instr(block)
            ir_index = get_block_ir_idx(block)
            block_name = block.name

            if not isinstance(instr, ChironAST.AssignmentCommand):
                skipped.append(
                    GVNSkip(region_id, block_name, ir_index, "non-assignment", str(instr))
                )
                active.clear()
                continue

            key, op, operand_vars, reason = _expr_key(instr.rexpr, block, ssa_info)
            if key is None:
                skipped.append(
                    GVNSkip(region_id, block_name, ir_index, reason, str(instr.rexpr))
                )
                active.clear()
                continue

            occurrence = CSEOccurrence(
                region_id=region_id,
                block_name=block_name,
                ir_index=ir_index,
                target=str(instr.lvar),
                expression=str(instr.rexpr),
                instr=instr,
            )

            if key not in active:
                active[key] = (next_group_id, operand_vars)
                groups[next_group_id] = {
                    "key": key,
                    "op": op,
                    "expression": str(instr.rexpr),
                    "occurrences": [occurrence],
                    "region_id": region_id,
                }
                next_group_id += 1
            else:
                group_id, _ = active[key]
                groups[group_id]["occurrences"].append(occurrence)

            defined_var = instr.lvar.varname
            for active_key, (_, active_operand_vars) in list(active.items()):
                if defined_var in active_operand_vars:
                    del active[active_key]

    candidates = []
    for group in groups.values():
        occurrences = tuple(group["occurrences"])
        if len(occurrences) < 2:
            continue
        candidates.append(
            CSECandidate(
                region_id=group["region_id"],
                expression_key=group["key"],
                op=group["op"],
                expression=group["expression"],
                occurrences=occurrences,
            )
        )

    candidates.sort(
        key=lambda candidate: (
            candidate.region_id,
            candidate.occurrences[0].ir_index,
            candidate.expression,
        )
    )

    region_names = tuple(tuple(block.name for block in region) for region in regions)
    return GVNInfo(
        regions=region_names,
        candidates=tuple(candidates),
        skipped=tuple(skipped),
    )


def dump_gvn_info(info):
    print("\n===== GVN/CSE PHASE 0 =====")
    print(f"  straight_line_regions={len(info.regions)}")
    print(f"  repeated_expression_candidates={len(info.candidates)}")

    for candidate in info.candidates:
        occs = ", ".join(
            f"{occ.target}@ir[{occ.ir_index}]/{occ.block_name}"
            for occ in candidate.occurrences
        )
        print(
            "  "
            f"region {candidate.region_id}: {candidate.expression} "
            f"op={candidate.op}; occurrences={occs}"
        )

    skipped_by_reason = defaultdict(int)
    for item in info.skipped:
        skipped_by_reason[item.reason] += 1
    if skipped_by_reason:
        skipped_summary = ", ".join(
            f"{reason}={count}" for reason, count in sorted(skipped_by_reason.items())
        )
        print(f"  skipped={skipped_summary}")

    print("===========================\n")


def run_gvn(ir, cfg, ssa_info, debug=False):
    info = collect_gvn_info(ir, cfg, ssa_info)
    run_gvn.last_info = info

    if debug:
        dump_gvn_info(info)

    return ir


run_gvn.last_info = GVNInfo()
