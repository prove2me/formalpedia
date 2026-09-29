-- Prove2me | solution 1 for invB2_pos_case
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:26:24.960947+00:00
-- url     : https://prove2.me/submissions/ac662812-6f90-4747-8383-401511e6b0d0

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





/-- The parent hypotenuse `3c - 2a - 2b` of a Pythagorean triple with positive legs and
positive hypotenuse is positive: the maximum of `2(a + b)/c` over the circle `a² + b² = c²`
is `2√2 < 3`. -/
theorem parent_hyp_pos_aux (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hpt : IsPT a b c) : 0 < -2 * a - 2 * b + 3 * c := by
  unfold IsPT at hpt
  nlinarith [sq_nonneg (3 * c - 2 * a - 2 * b), sq_nonneg (a - b), mul_pos ha hb]





theorem solution(a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hpt : IsPT a b c)
    (h3 : a + 2 * b > 2 * c) (h4 : 2 * a + b > 2 * c) :
    0 < (invB2 a b c).1 ∧ 0 < (invB2 a b c).2.1 ∧ 0 < (invB2 a b c).2.2 := by
  refine ⟨by simp only [invB2]; omega, by simp only [invB2]; omega, ?_⟩
  simpa [invB2] using parent_hyp_pos_aux a b c ha hb hc hpt
