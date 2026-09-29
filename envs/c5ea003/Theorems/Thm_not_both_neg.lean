-- Prove2me | Theorems.Thm_not_both_neg
-- name    : not_both_neg
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T02:10:49.975583+00:00
-- url     : https://prove2.me/theorems/e55b424a-cb0c-4751-abec-e9718b2680f5
-- title:
--   The two "small" branches cannot both fail.
-- statement:
--   **The two "small" branches cannot both fail.**  For a Pythagorean triple with positive
--   legs, `a + 2b ≤ 2c` and `2a + b ≤ 2c` are incompatible: squaring the first gives `4b ≤ 3a`
--   and squaring the second gives `4a ≤ 3b`.
--
--   ```lean
--   theorem not_both_neg(a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hpt : IsPT a b c)
--       (h1 : a + 2 * b ≤ 2 * c) (h2 : 2 * a + b ≤ 2 * c) : False := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/BerggrenTrees/BerggrenAux.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/BerggrenTrees/BerggrenAux.lean#L43

-- Thm stub generated from Applications/BerggrenTrees/BerggrenAux.lean
import Mathlib
import Definitions.Def_Applications_BerggrenTrees_BerggrenAux

/-! # Auxiliary notions for the Berggren tree of Pythagorean triples

This module supplies the vocabulary used by the Berggren catalog files: the
predicate `IsPT` recording that `(a, b, c)` is a Pythagorean triple, the three
inverse Barning–Hall maps `invB1`, `invB2`, `invB3` (the inverses of the three
matrices generating the tree of primitive triples), and the sign analysis of
their components.

The three matrices generating the Berggren (Barning–Hall) tree are

```
A₁ = !![1, -2, 2; 2, -1, 2; 2, -2, 3]
A₂ = !![1,  2, 2; 2,  1, 2; 2,  2, 3]
A₃ = !![-1, 2, 2; -2, 1, 2; -2, 2, 3]
```

and `invB1`, `invB2`, `invB3` below are the linear maps given by `A₁⁻¹`, `A₂⁻¹`
and `A₃⁻¹`.  All three have the same last component `3c - 2a - 2b`, the
"parent hypotenuse".
-/

theorem not_both_neg(a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hpt : IsPT a b c)
    (h1 : a + 2 * b ≤ 2 * c) (h2 : 2 * a + b ≤ 2 * c) : False := by sorry
