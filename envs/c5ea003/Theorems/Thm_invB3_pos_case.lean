-- Prove2me | Theorems.Thm_invB3_pos_case
-- name    : invB3_pos_case
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T02:10:44.111315+00:00
-- url     : https://prove2.me/theorems/bd5c01d3-db07-4eaa-a743-aae971e1bb9b
-- title:
--   Positivity of the third inverse branch: it applies when `a + 2b < 2c` and `2a + b > 2c`.
-- statement:
--   Positivity of the third inverse branch: it applies when `a + 2b < 2c` and `2a + b > 2c`.
--
--   ```lean
--   theorem invB3_pos_case(a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hpt : IsPT a b c)
--       (h3 : a + 2 * b < 2 * c) (h4 : 2 * a + b > 2 * c) :
--       0 < (invB3 a b c).1 ∧ 0 < (invB3 a b c).2.1 ∧ 0 < (invB3 a b c).2.2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/BerggrenTrees/BerggrenAux.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/BerggrenTrees/BerggrenAux.lean#L68

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

theorem invB3_pos_case(a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hpt : IsPT a b c)
    (h3 : a + 2 * b < 2 * c) (h4 : 2 * a + b > 2 * c) :
    0 < (invB3 a b c).1 ∧ 0 < (invB3 a b c).2.1 ∧ 0 < (invB3 a b c).2.2 := by sorry
