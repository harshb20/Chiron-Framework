"""
Phase 1/2 Global Value Numbering / Common Subexpression Elimination.

This pass records conservative local common-subexpression candidates over
straight-line CFG regions, then performs a narrow local rewrite for safe
repeated assignment expressions.
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
    target_version: int
    expression: str
    expression_key: tuple
    operand_versions: tuple
    instr: object


@dataclass(frozen=True)
class CSECandidate:
    region_id: int
    expression_key: tuple
    op: str
    expression: str
    occurrences: tuple

    @property
    def first_occurrence(self):
        return self.occurrences[0]

    @property
    def later_occurrences(self):
        return self.occurrences[1:]

    @property
    def first_ir_index(self):
        return self.first_occurrence.ir_index

    @property
    def later_ir_indices(self):
        return tuple(occ.ir_index for occ in self.later_occurrences)

    @property
    def destination_vars(self):
        return tuple(occ.target for occ in self.occurrences)


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
    (ChironAST.Div, "/", False),
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
        return ("num", expr.val), frozenset(), None

    if isinstance(expr, ChironAST.Var):
        version = ssa_info.var_version_use.get((expr.varname, block))
        if version is None or version < 0:
            return None, frozenset(), "missing operand version"
        return ("var", expr.varname, version), frozenset({expr.varname}), None

    return None, frozenset(), "unsupported operand"


def _expr_key(expr, block, ssa_info):
    for cls, op, commutative in _BINOP_INFO:
        if not isinstance(expr, cls):
            continue

        left_key, left_vars, left_reason = _operand_key(expr.lexpr, block, ssa_info)
        if left_key is None:
            return None, op, frozenset(), f"left {left_reason}"

        right_key, right_vars, right_reason = _operand_key(expr.rexpr, block, ssa_info)
        if right_key is None:
            return None, op, frozenset(), f"right {right_reason}"

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


def _invalidate_active_defs(active, defined_var):
    for active_key, (_, active_operand_vars) in list(active.items()):
        if defined_var in active_operand_vars:
            del active[active_key]


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

            defined_var = instr.lvar.varname
            target_version = ssa_info.instr_version_def.get((defined_var, block))
            if target_version is None:
                skipped.append(
                    GVNSkip(
                        region_id,
                        block_name,
                        ir_index,
                        "missing target version",
                        str(instr.lvar),
                    )
                )
                active.clear()
                continue

            key, op, operand_vars, reason = _expr_key(instr.rexpr, block, ssa_info)
            if key is None:
                skipped.append(
                    GVNSkip(region_id, block_name, ir_index, reason, str(instr.rexpr))
                )
                _invalidate_active_defs(active, defined_var)
                continue

            occurrence = CSEOccurrence(
                region_id=region_id,
                block_name=block_name,
                ir_index=ir_index,
                target=str(instr.lvar),
                target_version=target_version,
                expression=str(instr.rexpr),
                expression_key=key,
                operand_versions=tuple(
                    operand for operand in key[1:] if operand[0] == "var"
                ),
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

            _invalidate_active_defs(active, defined_var)

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


def _format_occurrence(occ):
    return (
        f"{occ.target}_v{occ.target_version}@ir[{occ.ir_index}]"
        f"/{occ.block_name}"
    )


def _skip_summary(skips):
    skipped_by_reason = defaultdict(int)
    for item in skips:
        skipped_by_reason[item.reason] += 1
    return ", ".join(
        f"{reason}={count}" for reason, count in sorted(skipped_by_reason.items())
    )


def dump_gvn_info(info):
    print("\n===== GVN/CSE PHASE 1 =====")
    print(f"  straight_line_regions={len(info.regions)}")
    print(f"  repeated_expression_candidates={len(info.candidates)}")

    candidates_by_region = defaultdict(list)
    for candidate in info.candidates:
        candidates_by_region[candidate.region_id].append(candidate)

    skips_by_region = defaultdict(list)
    for item in info.skipped:
        skips_by_region[item.region_id].append(item)

    for region_id, region in enumerate(info.regions):
        print(f"  region {region_id} blocks={list(region)}")

        region_candidates = candidates_by_region.get(region_id, [])
        if region_candidates:
            for candidate in region_candidates:
                first = candidate.first_occurrence
                later = ", ".join(
                    _format_occurrence(occ) for occ in candidate.later_occurrences
                )
                destinations = ", ".join(candidate.destination_vars)
                print(
                    "    candidate "
                    f"op={candidate.op} expr={candidate.expression} "
                    f"key={candidate.expression_key}"
                )
                print(f"      first={_format_occurrence(first)}")
                print(f"      later={later}")
                print(f"      destinations={destinations}")
        else:
            print("    candidates=none")

        region_skips = skips_by_region.get(region_id, [])
        if region_skips:
            print(f"    skipped={_skip_summary(region_skips)}")
            for item in region_skips:
                print(
                    "      skip "
                    f"{item.reason}: ir[{item.ir_index}]/{item.block_name} "
                    f"{item.detail}"
                )

    if info.skipped:
        print(f"  skipped_total={_skip_summary(info.skipped)}")

    print("===========================\n")


def _assignment_occurrence(ir, occurrence):
    ir_index = occurrence.ir_index
    if ir_index is None or ir_index < 0 or ir_index >= len(ir):
        return None

    instr = ir[ir_index][0]
    if not isinstance(instr, ChironAST.AssignmentCommand):
        return None
    if not isinstance(instr.lvar, ChironAST.Var):
        return None
    if instr.lvar.varname != occurrence.target:
        return None
    if str(instr.rexpr) != occurrence.expression:
        return None

    return instr


def _target_var(instr):
    if isinstance(instr, ChironAST.AssignmentCommand) and isinstance(
        instr.lvar, ChironAST.Var
    ):
        return instr.lvar.varname
    return None


def _var_redefined_between(ir, varname, first_index, later_index):
    if first_index is None or later_index is None or later_index <= first_index:
        return True

    for ir_index in range(first_index + 1, later_index):
        if _target_var(ir[ir_index][0]) == varname:
            return True

    return False


def _rewrite_candidate(ir, new_ir, candidate):
    if candidate.op not in {"+", "-", "*", "/"}:
        return False

    first = candidate.first_occurrence
    first_instr = _assignment_occurrence(ir, first)
    if first_instr is None:
        return False

    first_target = _target_var(first_instr)
    if first_target is None:
        return False

    changed = False
    for occurrence in candidate.later_occurrences:
        later_instr = _assignment_occurrence(ir, occurrence)
        if later_instr is None:
            continue
        if _assignment_occurrence(new_ir, occurrence) is None:
            continue

        later_target = _target_var(later_instr)
        if later_target is None or later_target == first_target:
            continue
        if _var_redefined_between(
            ir, first_target, first.ir_index, occurrence.ir_index
        ):
            continue

        new_ir[occurrence.ir_index] = (
            ChironAST.AssignmentCommand(
                later_instr.lvar, ChironAST.Var(first_target)
            ),
            ir[occurrence.ir_index][1],
        )
        changed = True

    return changed


def _apply_local_cse(ir, info):
    if not info.candidates:
        return ir

    new_ir = list(ir)
    changed = False

    for candidate in info.candidates:
        if _rewrite_candidate(ir, new_ir, candidate):
            changed = True

    return new_ir if changed else ir


def run_gvn(ir, cfg, ssa_info, debug=False):
    info = collect_gvn_info(ir, cfg, ssa_info)
    run_gvn.last_info = info

    if debug:
        dump_gvn_info(info)

    return _apply_local_cse(ir, info)


run_gvn.last_info = GVNInfo()
