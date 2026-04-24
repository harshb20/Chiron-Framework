import sys

sys.path.insert(0, "../ChironCore/")

import cfg.cfgBuilder as cfgB
import ChironAST.ChironAST as ChironAST

from submissionAI import run_interval


def _vars_in_expr(expr):
    if isinstance(expr, ChironAST.Var):
        return {expr.varname}
    if isinstance(expr, (ChironAST.BinArithOp, ChironAST.BinCondOp)):
        return _vars_in_expr(expr.lexpr) | _vars_in_expr(expr.rexpr)
    if isinstance(expr, (ChironAST.UnaryArithOp, ChironAST.NOT)):
        return _vars_in_expr(expr.expr)
    return set()


def _uses_repeat_counter(cond):
    return any("__rep_counter_" in var for var in _vars_in_expr(cond))


def _safe_condition_result(ir, info, result, duplicate_indices):
    ir_idx = result.ir_index
    if not isinstance(ir_idx, int):
        return None
    if ir_idx < 0 or ir_idx >= len(ir):
        return None
    if ir_idx in duplicate_indices:
        return None

    block = info.block_map.get(result.block_name)
    if block is None or block.name in ("START", "END"):
        return None
    if len(block.instrlist) != 1:
        return None

    block_instr, block_ir_idx = block.instrlist[0]
    if block_ir_idx != ir_idx:
        return None

    instr, jump_target = ir[ir_idx]
    if instr is not block_instr:
        return None
    if not isinstance(instr, ChironAST.ConditionCommand):
        return None

    if isinstance(instr.cond, (ChironAST.BoolTrue, ChironAST.BoolFalse)):
        return None
    if _uses_repeat_counter(instr.cond):
        return None
    if not isinstance(jump_target, int) or jump_target <= 0:
        return None

    return instr


def run_interval_rewrite(ir, cfg=None, debug=False):
    """Rewrite interval-proven branch conditions to BoolTrue/BoolFalse.

    The rewrite is intentionally narrow: it trusts only structured condition
    classifications produced from each condition block's IN state, and leaves
    branch offsets untouched for later CFG simplification.
    """
    if cfg is None:
        cfg = cfgB.buildCFG(ir, "opt_cfg_interval", isSingle=True)

    info = run_interval(ir, cfg=cfg, debug=debug)
    results = info.ordered_condition_results()

    counts = {}
    for result in results:
        counts[result.ir_index] = counts.get(result.ir_index, 0) + 1
    duplicate_indices = {ir_idx for ir_idx, count in counts.items() if count > 1}

    changed = False
    new_ir = list(ir)

    for result in results:
        if result.classification not in ("always_true", "always_false"):
            continue

        instr = _safe_condition_result(ir, info, result, duplicate_indices)
        if instr is None:
            continue

        replacement_cond = (
            ChironAST.BoolTrue()
            if result.classification == "always_true"
            else ChironAST.BoolFalse()
        )
        ir_idx = result.ir_index
        new_ir[ir_idx] = (ChironAST.ConditionCommand(replacement_cond), ir[ir_idx][1])
        changed = True

    return new_ir if changed else ir
