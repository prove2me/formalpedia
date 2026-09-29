-- Prove2me | solution 1 for JacSign.A_one_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T09:05:50.275985+00:00
-- url     : https://prove2.me/submissions/03e4e22d-99d4-46fc-9752-95a22e6ff1b0

-- Sol generated from Tropical/JacobiSignedWeilFloorBound.lean
import Mathlib
import Definitions.Def_Tropical_JacobiSignedWeilFloorBound
import Definitions.Def_Tropical_JacobiSignedWeilFloorCore
import Theorems.Thm_JacSign_chi_cube
import Theorems.Thm_JacSign_moment

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






/-- All square twists have the same character sum up to the sign `χ(c)`. -/
theorem A_sq_scale {c : ZMod p} (hc : c ≠ 0) :
    A p (c ^ 2) = quadraticChar (ZMod p) c * A p 1 := by
  have hre : A p (c ^ 2) = ∑ u : ZMod p, quadraticChar (ZMod p) ((c * u) ^ 3 - c ^ 2 * (c * u)) := by
    rw [A]
    exact (Fintype.sum_equiv (Equiv.mulLeft₀ c hc) _ _ fun u => rfl).symm
  rw [hre, A, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [show (c * u) ^ 3 - c ^ 2 * (c * u) = c ^ 3 * (u ^ 3 - 1 * u) by ring, map_mul, chi_cube]








open JacSign in
theorem solution(hp : p ≠ 2) (h1 : p % 4 = 1) : (A p 1) ^ 2 ≤ 4 * (p : ℤ) := by
  have hp2 := (Fact.out : p.Prime).two_le
  set F : ZMod p → ℤ := fun d => (A p d) ^ 2 with hFdef
  have hFnn : ∀ d, 0 ≤ F d := fun d => sq_nonneg _
  have hscale : ∀ c ∈ univ.erase (0 : ZMod p), F (c ^ 2) = (A p 1) ^ 2 := by
    intro c hc
    have hc0 : c ≠ 0 := (Finset.mem_erase.mp hc).1
    rw [hFdef]
    simp only
    rw [A_sq_scale p hc0, mul_pow, quadraticChar_sq_one hc0, one_mul]
  have hleft : ∑ c ∈ univ.erase (0 : ZMod p), F (c ^ 2) = ((p : ℤ) - 1) * (A p 1) ^ 2 := by
    rw [Finset.sum_congr rfl hscale, Finset.sum_const,
      Finset.card_erase_of_mem (Finset.mem_univ (0 : ZMod p)), Finset.card_univ, ZMod.card,
      nsmul_eq_mul]
    congr 1
    push_cast [Nat.cast_sub (by omega : 1 ≤ p)]
    ring
  have hfib : ∀ b : ZMod p,
      ((univ.erase (0 : ZMod p)).filter (fun c => c ^ 2 = b)).card ≤ 2 := by
    intro b
    by_cases hemp : ((univ.erase (0 : ZMod p)).filter (fun c => c ^ 2 = b)) = ∅
    · simp [hemp]
    · obtain ⟨c0, hc0⟩ := Finset.nonempty_of_ne_empty hemp
      have hsub : ((univ.erase (0 : ZMod p)).filter (fun c => c ^ 2 = b)) ⊆ {c0, -c0} := by
        intro c hc
        have hcb : c ^ 2 = b := (Finset.mem_filter.mp hc).2
        have hc0b : c0 ^ 2 = b := (Finset.mem_filter.mp hc0).2
        have hcc : c ^ 2 = c0 ^ 2 := by rw [hcb, hc0b]
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp hcc with h | h
        · simp [h]
        · simp [h]
      calc ((univ.erase (0 : ZMod p)).filter (fun c => c ^ 2 = b)).card
          ≤ ({c0, -c0} : Finset (ZMod p)).card := Finset.card_le_card hsub
        _ ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
  have hright : ∑ c ∈ univ.erase (0 : ZMod p), F (c ^ 2) ≤ 2 * ∑ d : ZMod p, F d := by
    rw [Finset.sum_comp F fun c : ZMod p => c ^ 2]
    have hle : ∑ b ∈ (univ.erase (0 : ZMod p)).image (fun c : ZMod p => c ^ 2),
        ((univ.erase (0 : ZMod p)).filter (fun c => c ^ 2 = b)).card • F b
        ≤ ∑ b ∈ (univ.erase (0 : ZMod p)).image (fun c : ZMod p => c ^ 2), 2 * F b := by
      refine Finset.sum_le_sum fun b _ => ?_
      rw [nsmul_eq_mul]
      have hb := hFnn b
      have hcard : (((univ.erase (0 : ZMod p)).filter (fun c => c ^ 2 = b)).card : ℤ) ≤ 2 := by
        exact_mod_cast hfib b
      exact mul_le_mul_of_nonneg_right hcard hb
    refine hle.trans ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun b _ _ => by positivity
  rw [hleft, moment p hp h1] at hright
  have hpos : (0 : ℤ) < (p : ℤ) - 1 := by
    have : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp2
    linarith
  nlinarith [hright, hpos]
