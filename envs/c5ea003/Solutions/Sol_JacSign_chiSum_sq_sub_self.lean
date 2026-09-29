-- Prove2me | solution 1 for JacSign.chiSum_sq_sub_self
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T08:58:09.523229+00:00
-- url     : https://prove2.me/submissions/24612624-d486-4e50-8eba-a16cbb2fd2aa

-- Sol generated from Tropical/JacobiSignedWeilFloorBound.lean
import Mathlib
import Definitions.Def_Tropical_JacobiSignedWeilFloorBound
import Definitions.Def_Tropical_JacobiSignedWeilFloorCore

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
theorem solution(hp : p ≠ 2) :
    ∑ u : ZMod p, quadraticChar (ZMod p) (u ^ 2 - u) = -1 := by
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp
  have h1 : ∑ u : ZMod p, quadraticChar (ZMod p) (u ^ 2 - u)
      = ∑ u ∈ univ.erase (0 : ZMod p), quadraticChar (ZMod p) (u ^ 2 - u) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod p))]; simp
  have h2 : ∀ u ∈ univ.erase (0 : ZMod p),
      quadraticChar (ZMod p) (u ^ 2 - u) = quadraticChar (ZMod p) (1 - u⁻¹) := by
    intro u hu
    have hu0 : u ≠ 0 := (Finset.mem_erase.mp hu).1
    have h : u ^ 2 - u = u ^ 2 * (1 - u⁻¹) := by field_simp
    rw [h, map_mul, quadraticChar_sq_one' hu0, one_mul]
  rw [h1, Finset.sum_congr rfl h2]
  have h3 : ∑ u ∈ univ.erase (0 : ZMod p), quadraticChar (ZMod p) (1 - u⁻¹)
      = ∑ v ∈ univ.erase (1 : ZMod p), quadraticChar (ZMod p) v := by
    refine Finset.sum_nbij' (i := fun u => 1 - u⁻¹) (j := fun v => (1 - v)⁻¹) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      have ha0 : a ≠ 0 := (Finset.mem_erase.mp ha).1
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      intro h
      have hinv : a⁻¹ = 0 := by linear_combination -h
      exact ha0 (by simpa using inv_eq_zero.mp hinv)
    · intro v hv
      have hv1 : v ≠ 1 := (Finset.mem_erase.mp hv).1
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      exact inv_ne_zero (sub_ne_zero.mpr (Ne.symm hv1))
    · intro a ha
      have ha0 : a ≠ 0 := (Finset.mem_erase.mp ha).1
      show (1 - (1 - a⁻¹))⁻¹ = a
      rw [show (1 : ZMod p) - (1 - a⁻¹) = a⁻¹ by ring, inv_inv]
    · intro v hv
      have hv1 : v ≠ 1 := (Finset.mem_erase.mp hv).1
      show 1 - ((1 - v)⁻¹)⁻¹ = v
      rw [inv_inv]; ring
    · intro a _; rfl
  rw [h3]
  have h4 := quadraticChar_sum_zero (F := ZMod p) hF
  have h5 : quadraticChar (ZMod p) 1
      + ∑ v ∈ univ.erase (1 : ZMod p), quadraticChar (ZMod p) v = 0 := by
    rw [Finset.add_sum_erase _ _ (Finset.mem_univ (1 : ZMod p))]; exact h4
  rw [MulChar.map_one] at h5
  linarith
