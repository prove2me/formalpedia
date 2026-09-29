-- Prove2me | solution 1 for JacSign.inner_T
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T09:01:21.066837+00:00
-- url     : https://prove2.me/submissions/b7d321cc-40bd-40fb-b94c-5d298a3b4c8d

-- Sol generated from Tropical/JacobiSignedWeilFloorBound.lean
import Mathlib
import Definitions.Def_Tropical_JacobiSignedWeilFloorBound
import Definitions.Def_Tropical_JacobiSignedWeilFloorCore
import Theorems.Thm_JacSign_chi_neg_one_eq_one

/-!
# The Weil floor for the Jacobi-signed circle count

This file proves, completely elementarily (no algebraic geometry, no Hasse bound
imported), the **Weil bound**

`W p ^ 2 ≤ 4 * p`

for the Jacobi-signed circle count `W p = ∑_x χ(x(1-x²))` of
`JacobiSignedWeilFloorCore.lean`.  Equivalently `|W p| ≤ 2 √p`: the JACSIGN
statistic sits exactly at the square-root noise floor of a character sum.

The proof is a second-moment (averaging over quadratic twists) argument:

* `JacSign.chiSum_quadratic` : `∑_d χ((d-a)(d-b)) = p-1` if `a = b` and `-1` otherwise;
* `JacSign.A p d = ∑_x χ(x³ - d x)` is the trace of Frobenius of `y² = x³ - d x`;
* `JacSign.A_sq_scale` : `A p (c²) = χ(c) · A p 1` — all *square* twists carry the
  same squared trace;
* `JacSign.moment` : `∑_d (A p d)² = 2 p (p-1)` — the exact second moment;
* since squaring is at most `2`-to-`1`, the `p-1` scalings contribute
  `(p-1) · (A p 1)² ≤ 2 · 2p(p-1)`, whence `(A p 1)² ≤ 4p`.
-/

open Finset

open JacSign

variable (p : ℕ) [Fact p.Prime]














open JacSign in
theorem solution(hp : p ≠ 2) (h1 : p % 4 = 1) (x : ZMod p) :
    (∑ y : ZMod p, if x ^ 2 = y ^ 2 then quadraticChar (ZMod p) (x * y) else 0)
      = if x = 0 then 0 else 2 := by
  have hchi1 : quadraticChar (ZMod p) (-1) = 1 := chi_neg_one_eq_one p h1
  have hset : (univ.filter (fun y : ZMod p => x ^ 2 = y ^ 2)) = {x, -x} := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro h
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp h.symm with h' | h'
      · exact Or.inl h'
      · exact Or.inr h'
    · rintro (rfl | rfl) <;> ring
  rw [← Finset.sum_filter, hset]
  by_cases hx : x = 0
  · subst hx; simp
  · rw [if_neg hx]
    have hne : x ≠ -x := by
      intro h
      rcases (ZMod.neg_eq_self_iff x).mp h.symm with h' | h'
      · exact hx h'
      · have hodd : p % 2 = 1 := (Fact.out : p.Prime).eq_two_or_odd.resolve_left hp
        omega
    have e1 : quadraticChar (ZMod p) (x * x) = 1 := by
      rw [← sq]; exact quadraticChar_sq_one' hx
    have e2 : quadraticChar (ZMod p) (x * -x) = 1 := by
      rw [show x * -x = (-1) * x ^ 2 by ring, map_mul, hchi1, one_mul, quadraticChar_sq_one' hx]
    rw [Finset.sum_pair hne, e1, e2]
    norm_num
