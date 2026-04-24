# GVN/CSE Phase 3 Test Notes

These tests stay within the existing narrow local CSE scope: same-region,
straight-line assignment RHS reuse over `+`, `-`, and `*` only.

| File | Phase 3 rewrite signal |
| --- | --- |
| `test_gvn_commutative_add_multi.tl` | One local `+` candidate group should be reused across `:a`, `:b`, and `:c`, even though `:b` uses swapped operands. The optimized IR should rewrite both later assignments to the first result variable. |
| `test_gvn_commutative_mul.tl` | One local `*` candidate group should be reused across `:a` and `:b` with swapped operands, rewriting `:b` to the first result variable. |
| `test_gvn_ordered_subtraction.tl` | `:x - :y` and `:y - :x` must remain distinct. The optimized IR should leave both subtraction assignments unchanged. |
