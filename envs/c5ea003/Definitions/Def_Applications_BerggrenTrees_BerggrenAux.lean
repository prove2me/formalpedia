-- Prove2me | Definitions.Def_Applications_BerggrenTrees_BerggrenAux
-- name    : Applications_BerggrenTrees_BerggrenAux
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:36:13.556569+00:00
-- url     : https://prove2.me/theorems/892574a3-ab64-4324-af87-a23fd871489c
-- title:
--   Aether Catalog definitions — Applications_BerggrenTrees_BerggrenAux
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.BerggrenTrees.BerggrenAux`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/BerggrenTrees/BerggrenAux.lean by skeleton subtraction
import Mathlib

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

/-- `(a, b, c)` is a Pythagorean triple. -/
def IsPT (a b c : ℤ) : Prop := a ^ 2 + b ^ 2 = c ^ 2

/-- The inverse of the first Berggren matrix, `A₁⁻¹ = !![1, 2, -2; -2, -1, 2; -2, -2, 3]`. -/
def invB1 (a b c : ℤ) : ℤ × ℤ × ℤ := (a + 2 * b - 2 * c, -2 * a - b + 2 * c, -2 * a - 2 * b + 3 * c)

/-- The inverse of the second Berggren matrix, `A₂⁻¹ = !![1, 2, -2; 2, 1, -2; -2, -2, 3]`. -/
def invB2 (a b c : ℤ) : ℤ × ℤ × ℤ := (a + 2 * b - 2 * c, 2 * a + b - 2 * c, -2 * a - 2 * b + 3 * c)

/-- The inverse of the third Berggren matrix, `A₃⁻¹ = !![-1, -2, 2; 2, 1, -2; -2, -2, 3]`. -/
def invB3 (a b c : ℤ) : ℤ × ℤ × ℤ := (-a - 2 * b + 2 * c, 2 * a + b - 2 * c, -2 * a - 2 * b + 3 * c)


