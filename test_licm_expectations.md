# LICM Test Expectations

These tests are source-level `.tl` files using only syntax already present in the repository: assignments, `repeat`, `if`/`else`, turtle movement commands, pen commands, and `goto`.

| File | Pattern | Current conservative LICM | Later SCCP/ADCE impact |
| --- | --- | --- | --- |
| `test_licm_hoist_basic.tl` | Basic invariant assignment used by movement | Expected to hoist `:step` | `--opt-all` may fold or propagate constants |
| `test_licm_no_hoist_variant.tl` | RHS depends on loop-carried `:i` | Expected not to hoist `:step` or `:i` update | SCCP/ADCE should preserve observable movement |
| `test_licm_no_hoist_div.tl` | Invariant-looking RHS contains division | Expected not to hoist `:chunk` under current Div safety rule | Later passes may simplify only if safe constants are propagated |
| `test_licm_chained_invariants.tl` | One invariant depends on another invariant in the same loop | Expected to hoist `:first` and `:second` in source order | `--opt-all` may propagate constants into movement |
| `test_licm_dead_invariant.tl` | Invariant assignment has no observable use | LICM may hoist `:dead` | ADCE may remove it under stronger pipelines |
| `test_licm_observable_use.tl` | Hoisted values feed `goto`, `forward`, and `right` | Expected to hoist `:gx` and `:gy` | SCCP may propagate constants, but observable commands should remain |
| `test_licm_no_dedicated_preheader.tl` | Branch-before-loop source-level approximation | The current `.tl` grammar lowers `repeat` with a dedicated counter-init preheader, so current LICM is expected to hoist `:candidate`; a true no-dedicated-preheader case needs an IR/unit-level test because source `goto` is turtle movement, not control flow | Later passes may simplify the guarding branch |
| `test_licm_multi_loop.tl` | Sequential loops with hoistable, variant, and Div-blocked patterns | Expected to hoist `:h1`; expected not to hoist `:variant` or `:blocked` | Later passes may fold constants and remove dead assignments |
| `test_licm_branch_inside_loop.tl` | Internal branch inside a loop with an invariant used on both paths | Expected to hoist `:dist` | SCCP may simplify if branch state becomes known; observable movement should remain |
| `test_licm_stress.tl` | Larger integration case with multiple loops, chained invariants, dead invariants, observable invariants, Div, varying values, and internal branches | Expected to hoist safe invariant assignments with dedicated preheaders; expected not to hoist Div-based or loop-carried assignments | `--opt-all` may fold, propagate, and remove dead invariants after LICM |

Note: the current source language has structured control flow only. It does not expose a control-flow `goto`, so a repeat-loop header without a dedicated preheader is not directly constructible as a plain `.tl` source file.
