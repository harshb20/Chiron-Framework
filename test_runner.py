import sys
import os

sys.path.insert(0, "ChironCore/")
sys.path.insert(0, "Submission/")

from ChironAST.builder import astGenPass
from irhandler import IRHandler, getParseTree
import cfg.cfgBuilder as cfgB
from ssa import SSAInfo
from sccp import SCCP
from adce import run_adce, dump_adce

def test_file(filepath):
    irHandler = IRHandler("")
    parseTree = getParseTree(filepath)
    astgen = astGenPass()
    ir = astgen.visitStart(parseTree)
    irHandler.setIR(ir)
    cfg = cfgB.buildCFG(ir, "opt_cfg", isSingle=True)

    ssa_info = SSAInfo(cfg)
    ssa_info.build()
    ssa_info.dump()

    sccp_result = SCCP(cfg, ssa_info)
    sccp_result.run()
    sccp_result.dump()

    executable_blocks = sccp_result.executable_blocks
    live_blocks = run_adce(cfg, ssa_info, executable_blocks)
    dump_adce(live_blocks, executable_blocks, ssa_info)

if __name__ == "__main__":
    test_file("../test_phi_instr_same_block.tl")
