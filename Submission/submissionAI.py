import copy
from dataclasses import dataclass, field
import math
from pathlib import Path
import sys
from typing import Any, Dict, List, Optional

CHIRON_CORE_DIR = Path(__file__).resolve().parents[1] / "ChironCore"
if str(CHIRON_CORE_DIR) not in sys.path:
    sys.path.insert(0, str(CHIRON_CORE_DIR))

import cfg.cfgBuilder as cfgB
from lattice import  *
import ChironAST.ChironAST as ChironAST


INF = math.inf
MAX_MAG = 10**6


class IntervalDomain(Lattice):
    """Integer interval [low, high] with ±∞ bounds and widening."""

    def __init__(self, data=None):
        if data is None:
            self.low, self.high = -INF, INF
        elif isinstance(data, IntervalDomain):
            self.low, self.high = data.low, data.high
        elif isinstance(data, tuple):
            self.low, self.high = data
        elif isinstance(data, int):
            self.low = self.high = data
        else:
            self.low, self.high = -INF, INF

    def __str__(self):
        if self.isBot():
            return "_|_"
        lo = "-inf" if self.low == -INF else str(self.low)
        hi = "+inf" if self.high == INF else str(self.high)
        return f"[{lo}, {hi}]"

    def __repr__(self):
        return self.__str__()

    def isBot(self):
        return self.low > self.high

    def isTop(self):
        return self.low == -INF and self.high == INF

    def meet(self, other):
        if self.isBot() or other.isBot():
            return IntervalDomain((1, 0))
        return IntervalDomain((max(self.low, other.low), min(self.high, other.high)))

    def join(self, other):
        if self.isBot():
            return IntervalDomain(other)
        if other.isBot():
            return IntervalDomain(self)
        lo = min(self.low, other.low)
        hi = max(self.high, other.high)
        if lo != -INF and lo < -MAX_MAG:
            lo = -INF
        if hi != INF and hi > MAX_MAG:
            hi = INF
        return IntervalDomain((lo, hi))

    def __le__(self, other):
        if self.isBot():
            return True
        if other.isBot():
            return False
        return other.low <= self.low and self.high <= other.high

    def __eq__(self, other):
        if not isinstance(other, IntervalDomain):
            return False
        return self.low == other.low and self.high == other.high

    def __ne__(self, other):
        return not self.__eq__(other)

    def __hash__(self):
        return hash((self.low, self.high))

    # Abstract arithmetic transformers
    def __add__(self, other):
        if self.isBot() or other.isBot():
            return IntervalDomain((1, 0))
        return IntervalDomain((self.low + other.low, self.high + other.high))

    def __sub__(self, other):
        if self.isBot() or other.isBot():
            return IntervalDomain((1, 0))
        return IntervalDomain((self.low - other.high, self.high - other.low))

    def __mul__(self, other):
        if self.isBot() or other.isBot():
            return IntervalDomain((1, 0))
        prods = []
        for a in (self.low, self.high):
            for b in (other.low, other.high):
                try:
                    prods.append(a * b)
                except Exception:
                    prods.append(INF)
        prods = [p for p in prods if not (isinstance(p, float) and math.isnan(p))]
        if not prods:
            return IntervalDomain((-INF, INF))
        return IntervalDomain((min(prods), max(prods)))

    def __truediv__(self, other):
        if self.isBot() or other.isBot():
            return IntervalDomain((1, 0))
        if other.low <= 0 <= other.high:
            return IntervalDomain((-INF, INF))
        quots = []
        for a in (self.low, self.high):
            for b in (other.low, other.high):
                try:
                    if abs(b) == INF:
                        quots.append(0)
                    else:
                        quots.append(int(a // b) if a not in (INF, -INF) else (INF if (a > 0) == (b > 0) else -INF))
                except Exception:
                    quots.append(INF)
        return IntervalDomain((min(quots), max(quots)))

    def __neg__(self):
        if self.isBot():
            return IntervalDomain((1, 0))
        return IntervalDomain((-self.high, -self.low))


TOP = IntervalDomain((-INF, INF))
BOT = IntervalDomain((1, 0))


def _fmt_state(state):
    if not state:
        return "{}"
    items = sorted(state.items())
    return "{" + ", ".join(f"{k}={v}" for k, v in items) + "}"


def _block_sort_key(b):
    if b.name == "START":
        return -1
    if b.name == "END":
        return 10**9
    if b.instrlist:
        return b.instrlist[0][1]
    return 0


def _ordered_blocks(cfg):
    return sorted(list(cfg.nodes()), key=_block_sort_key)


@dataclass
class ConditionIntervalResult:
    """Interval-based classification for a ConditionCommand block."""

    block_name: str
    ir_index: Optional[int]
    condition: Any
    classification: str
    lhs_interval: Optional[IntervalDomain] = None
    rhs_interval: Optional[IntervalDomain] = None
    operator: Optional[str] = None


@dataclass
class IntervalInfo:
    """Structured interval-analysis result for later optimizer phases."""

    cfg: Any
    bb_in: Dict[str, Dict[str, IntervalDomain]]
    bb_out: Dict[str, List[Dict[str, IntervalDomain]]]
    block_order: List[str]
    block_map: Dict[str, Any]
    iterations: int = 0
    converged: bool = True
    visit_count: Dict[str, int] = field(default_factory=dict)
    iter_cap: Optional[int] = None
    widening_after: Optional[int] = None
    condition_results: Dict[str, ConditionIntervalResult] = field(default_factory=dict)

    def ordered_blocks(self):
        return [self.block_map[name] for name in self.block_order if name in self.block_map]

    def ordered_condition_results(self):
        return [
            self.condition_results[b.name]
            for b in self.ordered_blocks()
            if b.name in self.condition_results
        ]

    def format_state(self, state):
        return _fmt_state(state)

    def format_lines(self):
        lines = ["===== INTERVAL ANALYSIS ====="]
        for b in self.ordered_blocks():
            instr_str = ""
            if b.instrlist:
                instr_str = str(b.instrlist[0][0])
            lines.append(f"  [{b.name}] {instr_str}")
            lines.append(f"    IN : {self.format_state(self.bb_in.get(b.name, {}))}")
            out = self.bb_out.get(b.name, [])
            if len(out) == 2:
                lines.append(f"    OUT[true] : {self.format_state(out[0])}")
                lines.append(f"    OUT[false]: {self.format_state(out[1])}")
            elif len(out) == 1:
                lines.append(f"    OUT: {self.format_state(out[0])}")
            else:
                lines.append("    OUT: (none)")
        lines.append("=============================")
        return lines


class IntervalTransferFunction(TransferFunction):
    def __init__(self):
        pass

    def transferFunction(self, currBBIN, currBB):
        """Apply the instruction in currBB to its IN state, return OUT list.
        Returns [out] for non-branch, [trueOut, falseOut] for ConditionCommand.
        """
        state = copy.deepcopy(currBBIN) if currBBIN else {}

        if not currBB.instrlist:
            return [state]

        instr = currBB.instrlist[0][0]

        if isinstance(instr, ChironAST.AssignmentCommand):
            val = self._eval(instr.rexpr, state)
            state[instr.lvar.varname] = val
            return [state]

        if isinstance(instr, ChironAST.ConditionCommand):
            trueState = copy.deepcopy(state)
            falseState = copy.deepcopy(state)
            self._narrow(instr.cond, trueState, falseState)
            return [trueState, falseState]

        # MoveCommand, PenCommand, GotoCommand, NoOp, Pause — no state change
        return [state]

    def _eval(self, expr, state):
        if isinstance(expr, ChironAST.Num):
            return IntervalDomain((expr.val, expr.val))
        if isinstance(expr, ChironAST.Var):
            return state.get(expr.varname, IntervalDomain((-INF, INF)))
        if isinstance(expr, ChironAST.Sum):
            return self._eval(expr.lexpr, state) + self._eval(expr.rexpr, state)
        if isinstance(expr, ChironAST.Diff):
            return self._eval(expr.lexpr, state) - self._eval(expr.rexpr, state)
        if isinstance(expr, ChironAST.Mult):
            return self._eval(expr.lexpr, state) * self._eval(expr.rexpr, state)
        if isinstance(expr, ChironAST.Div):
            return self._eval(expr.lexpr, state) / self._eval(expr.rexpr, state)
        if isinstance(expr, ChironAST.UMinus):
            return -self._eval(expr.expr, state)
        return IntervalDomain((-INF, INF))

    def _narrow(self, cond, trueState, falseState):
        """Conservative narrowing: handle Var OP Var/Num for the 6 comparison ops.
        Anything more complex leaves states unchanged.
        """
        if not isinstance(cond, (ChironAST.LT, ChironAST.GT, ChironAST.LTE,
                                 ChironAST.GTE, ChironAST.EQ, ChironAST.NEQ)):
            return

        L, R = cond.lexpr, cond.rexpr
        lVal = self._eval(L, trueState)
        rVal = self._eval(R, trueState)

        def set_var(state, var, iv):
            if isinstance(var, ChironAST.Var):
                state[var.varname] = state.get(var.varname, IntervalDomain((-INF, INF))).meet(iv)

        if isinstance(cond, ChironAST.LT):
            # true:  L < R  => L.high <= R.high-1, R.low >= L.low+1
            set_var(trueState, L, IntervalDomain((-INF, rVal.high - 1)))
            set_var(trueState, R, IntervalDomain((lVal.low + 1, INF)))
            # false: L >= R
            set_var(falseState, L, IntervalDomain((rVal.low, INF)))
            set_var(falseState, R, IntervalDomain((-INF, lVal.high)))

        elif isinstance(cond, ChironAST.GT):
            # true:  L > R
            set_var(trueState, L, IntervalDomain((rVal.low + 1, INF)))
            set_var(trueState, R, IntervalDomain((-INF, lVal.high - 1)))
            # false: L <= R
            set_var(falseState, L, IntervalDomain((-INF, rVal.high)))
            set_var(falseState, R, IntervalDomain((lVal.low, INF)))

        elif isinstance(cond, ChironAST.LTE):
            set_var(trueState, L, IntervalDomain((-INF, rVal.high)))
            set_var(trueState, R, IntervalDomain((lVal.low, INF)))
            set_var(falseState, L, IntervalDomain((rVal.low + 1, INF)))
            set_var(falseState, R, IntervalDomain((-INF, lVal.high - 1)))

        elif isinstance(cond, ChironAST.GTE):
            set_var(trueState, L, IntervalDomain((rVal.low, INF)))
            set_var(trueState, R, IntervalDomain((-INF, lVal.high)))
            set_var(falseState, L, IntervalDomain((-INF, rVal.high - 1)))
            set_var(falseState, R, IntervalDomain((lVal.low + 1, INF)))

        elif isinstance(cond, ChironAST.EQ):
            # true: L == R  => both narrow to intersection
            inter = lVal.meet(rVal)
            set_var(trueState, L, inter)
            set_var(trueState, R, inter)
            # false: no narrowing (can't express "not equal" as a single interval)

        elif isinstance(cond, ChironAST.NEQ):
            # true: L != R, no narrowing
            # false: L == R, both narrow to intersection
            inter = lVal.meet(rVal)
            set_var(falseState, L, inter)
            set_var(falseState, R, inter)


class ForwardAnalysis():
    def __init__(self):
        self.transferFunctionInstance = IntervalTransferFunction()
        self.type = "IntervalTF"

    def initialize(self, currBB, isStartNode):
        return {}

    def isEqual(self, dA, dB):
        for i in dA.keys():
            if i not in dB.keys():
                return False
            if dA[i] != dB[i]:
                return False
        return True

    def meet(self, predList):
        """Join predecessor states: union of intervals per variable."""
        assert isinstance(predList, list)
        if not predList:
            return {}

        all_vars = set()
        for pred in predList:
            all_vars.update(pred.keys())

        result = {}
        for var in all_vars:
            joined = None
            for pred in predList:
                val = pred.get(var, IntervalDomain((-INF, INF)))
                joined = val if joined is None else joined.join(val)
            result[var] = joined
        return result


def _condition_result(
    block,
    classification,
    lhs_interval=None,
    rhs_interval=None,
    operator=None,
):
    instr, ir_index = block.instrlist[0]
    return ConditionIntervalResult(
        block_name=block.name,
        ir_index=ir_index,
        condition=instr.cond,
        classification=classification,
        lhs_interval=lhs_interval,
        rhs_interval=rhs_interval,
        operator=operator,
    )


def _is_singleton(iv):
    return not iv.isBot() and iv.low == iv.high


def _is_disjoint(left, right):
    return left.high < right.low or right.high < left.low


def _classify_interval_comparison(cond, left, right):
    if left.isBot() or right.isBot():
        return "unknown"

    if isinstance(cond, ChironAST.LT):
        if left.high < right.low:
            return "always_true"
        if left.low >= right.high:
            return "always_false"
        return "unknown"

    if isinstance(cond, ChironAST.LTE):
        if left.high <= right.low:
            return "always_true"
        if left.low > right.high:
            return "always_false"
        return "unknown"

    if isinstance(cond, ChironAST.GT):
        if left.low > right.high:
            return "always_true"
        if left.high <= right.low:
            return "always_false"
        return "unknown"

    if isinstance(cond, ChironAST.GTE):
        if left.low >= right.high:
            return "always_true"
        if left.high < right.low:
            return "always_false"
        return "unknown"

    if isinstance(cond, ChironAST.EQ):
        if _is_singleton(left) and _is_singleton(right) and left.low == right.low:
            return "always_true"
        if _is_disjoint(left, right):
            return "always_false"
        return "unknown"

    if isinstance(cond, ChironAST.NEQ):
        if _is_singleton(left) and _is_singleton(right) and left.low == right.low:
            return "always_false"
        if _is_disjoint(left, right):
            return "always_true"
        return "unknown"

    return "unknown"


def _classify_condition_block(block, in_state, evaluator):
    instr = block.instrlist[0][0]
    cond = instr.cond

    if isinstance(cond, ChironAST.BoolTrue):
        return _condition_result(block, "always_true")
    if isinstance(cond, ChironAST.BoolFalse):
        return _condition_result(block, "always_false")

    supported = (ChironAST.LT, ChironAST.GT, ChironAST.LTE,
                 ChironAST.GTE, ChironAST.EQ, ChironAST.NEQ)
    if not isinstance(cond, supported):
        return _condition_result(block, "unknown")

    try:
        left = evaluator._eval(cond.lexpr, in_state)
        right = evaluator._eval(cond.rexpr, in_state)
    except Exception:
        return _condition_result(block, "unknown", operator=cond.symbol)

    classification = _classify_interval_comparison(cond, left, right)
    return _condition_result(
        block,
        classification,
        lhs_interval=left,
        rhs_interval=right,
        operator=cond.symbol,
    )


def _classify_conditions(info):
    evaluator = IntervalTransferFunction()
    results = {}
    for block in info.ordered_blocks():
        if not block.instrlist:
            continue
        instr = block.instrlist[0][0]
        if not isinstance(instr, ChironAST.ConditionCommand):
            continue
        in_state = info.bb_in.get(block.name, {})
        results[block.name] = _classify_condition_block(block, in_state, evaluator)
    return results


def _run_worklist_info(cfg, analysis, debug=False):
    """Inline worklist loop — mirrors AI.AbstractInterpreter.worklistAlgorithm
    but skips the Interpreter base class (which the framework's
    AbstractInterpreter forgets to pass params to)."""
    from queue import Queue

    BBlist = list(cfg.nodes())
    bbIn = {}
    bbOut = {}
    for b in BBlist:
        bbIn[b.name] = analysis.initialize(b, b.name == "START")
        bbOut[b.name] = []

    wl = Queue()
    for b in BBlist:
        if b.name != "END":
            wl.put(b)

    def _different(dA, dB):
        if set(dA.keys()) != set(dB.keys()):
            return True
        for k in dA:
            if dA[k] != dB[k]:
                return True
        return False

    def _changed(newOut, oldOut):
        if len(newOut) != len(oldOut):
            return True
        return any(_different(newOut[i], oldOut[i]) for i in range(len(newOut)))

    iter_cap = 5000
    iters = 0
    visit_count = {}
    WIDEN_AFTER = 3

    while not wl.empty() and iters < iter_cap:
        iters += 1
        currBB = wl.get()
        oldOut = bbOut[currBB.name]
        oldIn = bbIn[currBB.name]
        visit_count[currBB.name] = visit_count.get(currBB.name, 0) + 1

        preds = list(cfg.predecessors(currBB))
        inlist = []
        for pred in preds:
            label = cfg.get_edge_label(pred, currBB)
            if bbOut[pred.name]:
                if label != "Cond_False":
                    inlist.append(bbOut[pred.name][0])
                else:
                    if len(bbOut[pred.name]) > 1:
                        inlist.append(bbOut[pred.name][1])
                    else:
                        inlist.append(bbOut[pred.name][0])

        if inlist:
            newIn = analysis.meet(inlist)
            # Classical widening: once a block has been revisited enough times,
            # any bound that moved outward compared to the previous IN gets
            # pushed to ±∞ to force termination.
            if visit_count[currBB.name] >= WIDEN_AFTER and oldIn:
                for var, iv in list(newIn.items()):
                    old_iv = oldIn.get(var)
                    if old_iv is None:
                        continue
                    lo = iv.low if iv.low >= old_iv.low else -INF
                    hi = iv.high if iv.high <= old_iv.high else INF
                    if lo != iv.low or hi != iv.high:
                        newIn[var] = IntervalDomain((lo, hi))
            bbIn[currBB.name] = newIn

        tf = analysis.transferFunctionInstance
        newOut = tf.transferFunction(bbIn[currBB.name], currBB)
        assert isinstance(newOut, list)
        bbOut[currBB.name] = newOut

        if _changed(newOut, oldOut):
            for succ in cfg.successors(currBB):
                wl.put(succ)

    converged = wl.empty()
    if debug and not converged:
        print(f"Interval analysis hit iteration cap ({iter_cap}) before convergence.")

    blocks = _ordered_blocks(cfg)
    info = IntervalInfo(
        cfg=cfg,
        bb_in=bbIn,
        bb_out=bbOut,
        block_order=[b.name for b in blocks],
        block_map={b.name: b for b in blocks},
        iterations=iters,
        converged=converged,
        visit_count=visit_count,
        iter_cap=iter_cap,
        widening_after=WIDEN_AFTER,
    )
    info.condition_results = _classify_conditions(info)
    return info


def _run_worklist(cfg, analysis):
    """Backward-compatible private wrapper for callers expecting IN/OUT maps."""
    info = _run_worklist_info(cfg, analysis)
    return info.bb_in, info.bb_out


def run_interval(ir, cfg=None, debug=False):
    """Run interval analysis without mutating or rewriting the IR.

    Args:
        ir: A Chiron IR list, or an IRHandler-like object with ``ir``/``cfg``.
        cfg: Optional CFG to reuse. If omitted, a single-instruction CFG is built.
        debug: If true, prints minimal solver convergence diagnostics.

    Returns:
        IntervalInfo with structured IN/OUT states and solver metadata.
    """
    if cfg is None and hasattr(ir, "cfg"):
        cfg = ir.cfg
    if hasattr(ir, "ir"):
        ir = ir.ir
    if cfg is None:
        cfg = cfgB.buildCFG(ir, "ai_cfg", isSingle=True)
    analysis = ForwardAnalysis()
    return _run_worklist_info(cfg, analysis, debug=debug)


def print_interval_info(info):
    print()
    for line in info.format_lines():
        print(line)
    print()


def analyzeUsingAI(irHandler):
    """Run interval analysis on the IR's CFG and print results per block."""
    cfg = irHandler.cfg
    if cfg is None:
        cfg = cfgB.buildCFG(irHandler.ir, "ai_cfg", isSingle=True)
        irHandler.setCFG(cfg)
    info = run_interval(irHandler.ir, cfg=cfg)
    print_interval_info(info)
    return info
