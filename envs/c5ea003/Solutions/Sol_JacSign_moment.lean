-- Prove2me | solution 1 for JacSign.moment
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T09:03:33.841856+00:00
-- url     : https://prove2.me/submissions/3611fdae-c944-4205-be64-527d03f5b4db

-- Sol generated from Tropical/JacobiSignedWeilFloorBound.lean
import Mathlib
import Definitions.Def_Tropical_JacobiSignedWeilFloorBound
import Definitions.Def_Tropical_JacobiSignedWeilFloorCore
import Theorems.Thm_JacSign_chiSum_quadratic
import Theorems.Thm_JacSign_inner_T

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
theorem solution(hp : p ≠ 2) (h1 : p % 4 = 1) :
    ∑ d : ZMod p, (A p d) ^ 2 = 2 * (p : ℤ) * ((p : ℤ) - 1) := by
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp
  have hp2 := (Fact.out : p.Prime).two_le
  have hstep1 : ∀ d : ZMod p, (A p d) ^ 2
      = ∑ x : ZMod p, ∑ y : ZMod p,
          quadraticChar (ZMod p) (x * y) *
            quadraticChar (ZMod p) ((d - x ^ 2) * (d - y ^ 2)) := by
    intro d
    rw [sq, A, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [← map_mul, ← map_mul]
    congr 1
    ring
  rw [Finset.sum_congr rfl fun d _ => hstep1 d, Finset.sum_comm]
  have hswap : ∀ x : ZMod p, (∑ d : ZMod p, ∑ y : ZMod p,
        quadraticChar (ZMod p) (x * y) * quadraticChar (ZMod p) ((d - x ^ 2) * (d - y ^ 2)))
      = ∑ y : ZMod p, quadraticChar (ZMod p) (x * y) *
          (if x ^ 2 = y ^ 2 then (p : ℤ) - 1 else -1) := by
    intro x
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Finset.mul_sum, chiSum_quadratic p hp (x ^ 2) (y ^ 2)]
  rw [Finset.sum_congr rfl fun x _ => hswap x]
  have hterm : ∀ x y : ZMod p,
      quadraticChar (ZMod p) (x * y) * (if x ^ 2 = y ^ 2 then (p : ℤ) - 1 else -1)
        = (if x ^ 2 = y ^ 2 then quadraticChar (ZMod p) (x * y) else 0) * (p : ℤ)
          - quadraticChar (ZMod p) x * quadraticChar (ZMod p) y := by
    intro x y
    by_cases h : x ^ 2 = y ^ 2
    · rw [if_pos h, if_pos h, map_mul]; ring
    · rw [if_neg h, if_neg h, map_mul]; ring
  simp only [hterm, Finset.sum_sub_distrib]
  have hT : ∑ x : ZMod p, ∑ y : ZMod p,
      (if x ^ 2 = y ^ 2 then quadraticChar (ZMod p) (x * y) else 0) * (p : ℤ)
      = 2 * ((p : ℤ) - 1) * (p : ℤ) := by
    simp only [← Finset.sum_mul]
    rw [Finset.sum_congr rfl fun x _ => inner_T p hp h1 x]
    congr 1
    rw [Finset.sum_ite]
    have h : (univ.filter (fun x : ZMod p => ¬ x = 0)) = univ.erase 0 := by
      ext x; simp [Finset.mem_erase, and_comm]
    rw [h, Finset.sum_const, Finset.sum_const,
      Finset.card_erase_of_mem (Finset.mem_univ (0 : ZMod p)), Finset.card_univ, ZMod.card]
    simp only [smul_zero, zero_add, nsmul_eq_mul]
    push_cast [Nat.cast_sub (by omega : 1 ≤ p)]
    ring
  have hzero : ∑ x : ZMod p, ∑ y : ZMod p,
      quadraticChar (ZMod p) x * quadraticChar (ZMod p) y = 0 := by
    rw [← Finset.sum_mul_sum, quadraticChar_sum_zero hF, mul_zero]
  rw [hT, hzero, sub_zero]
  ring
