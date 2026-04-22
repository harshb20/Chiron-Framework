# GVN/CSE Local Test Notes

These tests are source-level `.tl` files using existing assignment, arithmetic, and movement syntax only.

| File | Expected local GVN/CSE behavior |
| --- | --- |
| `test_gvn_same_block_repeated.tl` | Should expose one repeated `:x + 5` candidate in a straight-line local region, with occurrences at `:a` and `:b`. |
| `test_gvn_operand_redefined.tl` | Should not report the two `:x + 5` expressions as the same candidate because `:x` is redefined between `:a` and `:b`. |
| `test_gvn_commutative_add.tl` | Under `--opt-gvn`, should rewrite `:b = :y + :x` to reuse the first `:x + :y` result. |
| `test_gvn_commutative_mult.tl` | Under `--opt-gvn`, should rewrite `:b = :y * :x` to reuse the first `:x * :y` result. |
| `test_gvn_ordered_subtraction.tl` | Under `--opt-gvn`, should preserve `:b = :y - :x` and not reuse the earlier `:x - :y`. |
