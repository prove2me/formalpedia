-- Prove2me | solution 1 for JacSign.chiSum_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T08:59:41.302244+00:00
-- url     : https://prove2.me/submissions/32cb54d4-31ca-4461-8189-77e7f4f35fac

-- Sol generated from Tropical/JacobiSignedWeilFloorBound.lean
import Mathlib
import Definitions.Def_Tropical_JacobiSignedWeilFloorBound
import Definitions.Def_Tropical_JacobiSignedWeilFloorCore
import Theorems.Thm_JacSign_chiSum_sq_sub_self

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
theorem solution(hp : p ≠ 2) (a b : ZMod p) :
    ∑ d : ZMod p, quadraticChar (ZMod p) ((d - a) * (d - b))
      = if a = b then (p : ℤ) - 1 else -1 := by
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl]
    have hval : ∀ d : ZMod p, quadraticChar (ZMod p) ((d - a) * (d - a))
        = if d = a then 0 else 1 := by
      intro d
      by_cases hd : d = a
      · simp [hd]
      · rw [if_neg hd, ← sq]
        exact quadraticChar_sq_one' (sub_ne_zero.mpr hd)
    rw [Finset.sum_congr rfl fun d _ => hval d, Finset.sum_ite]
    have h : (univ.filter (fun x : ZMod p => ¬ x = a)) = univ.erase a := by
      ext x; simp [Finset.mem_erase, and_comm]
    have hp2 := (Fact.out : p.Prime).two_le
    rw [Finset.sum_const, Finset.sum_const, h,
      Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, ZMod.card]
    simp only [smul_zero, zero_add, nsmul_eq_mul, mul_one]
    push_cast [Nat.cast_sub (by omega : 1 ≤ p)]
    ring
  · have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
    have hre : ∑ d : ZMod p, quadraticChar (ZMod p) ((d - a) * (d - b))
        = ∑ u : ZMod p, quadraticChar (ZMod p)
            ((((Equiv.mulLeft₀ (b - a) hba).trans (Equiv.addLeft a)) u - a) *
             (((Equiv.mulLeft₀ (b - a) hba).trans (Equiv.addLeft a)) u - b)) :=
      (Fintype.sum_equiv ((Equiv.mulLeft₀ (b - a) hba).trans (Equiv.addLeft a)) _ _
        fun u => rfl).symm
    rw [hre]
    have hval : ∀ u : ZMod p,
        ((((Equiv.mulLeft₀ (b - a) hba).trans (Equiv.addLeft a)) u - a) *
         (((Equiv.mulLeft₀ (b - a) hba).trans (Equiv.addLeft a)) u - b))
          = (b - a) ^ 2 * (u ^ 2 - u) := by
      intro u
      show (a + (b - a) * u - a) * (a + (b - a) * u - b) = (b - a) ^ 2 * (u ^ 2 - u)
      ring
    simp only [hval, map_mul, quadraticChar_sq_one' hba, one_mul]
    rw [chiSum_sq_sub_self p hp, if_neg hab]
