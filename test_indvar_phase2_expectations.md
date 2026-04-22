# INDVAR Phase 2 Test Notes

These tests are source-level `.tl` files using existing assignment, `repeat`, arithmetic, and movement syntax only.

| File | Phase 2 detection signal |
| --- | --- |
| `test_indvar_derived_mul.tl` | Should expose `:i = :i + 1` as a basic induction variable and `:d = :i * 4` as a multiplicative derived induction-variable candidate. |
| `test_indvar_derived_add.tl` | Should expose `:j = :j + 2` as a basic induction variable and `:y = :j + 7` as an additive derived induction-variable candidate. |
