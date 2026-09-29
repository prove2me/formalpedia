-- Prove2me | solution 1 for not_both_neg
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:26:26.055273+00:00
-- url     : https://prove2.me/submissions/29a8f88c-960c-4e8c-8300-ca92c063e0ba

-- Sol generated from Applications/BerggrenTrees/BerggrenAux.lean
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










theorem solution(a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hpt : IsPT a b c)
    (h1 : a + 2 * b ≤ 2 * c) (h2 : 2 * a + b ≤ 2 * c) : False := by
  unfold IsPT at hpt
  have hc : 0 < c := by nlinarith
  have hb' : 4 * b ≤ 3 * a := by nlinarith
  have ha' : 4 * a ≤ 3 * b := by nlinarith
  nlinarith
