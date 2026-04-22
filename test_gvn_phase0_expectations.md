# GVN/CSE Phase 0 Test Notes

These tests are source-level `.tl` files using existing assignment, arithmetic, and movement syntax only.

| File | Phase 0 detection signal |
| --- | --- |
| `test_gvn_same_block_repeated.tl` | Should expose one repeated `:x + 5` candidate in a straight-line local region, with occurrences at `:a` and `:b`. |
| `test_gvn_operand_redefined.tl` | Should not report the two `:x + 5` expressions as the same candidate because `:x` is redefined between `:a` and `:b`. |
