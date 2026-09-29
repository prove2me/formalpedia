-- Prove2me | solution 1 for mme_entropy_lower_of_scaled_atom_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T23:57:26.392904+00:00
-- url     : https://prove2.me/submissions/6e0d33ba-41eb-4186-be4c-0569341e166f

import Theorems.Thm_mme_regional_mass_entropy_algebra
import Theorems.Thm_mme_released_116_regional_split_mass
import Definitions.Def_mme_regional_split_entropy_data

open BigOperators MME MME.RegionRate MME.RecursiveThinSplit
set_option autoImplicit false

/-- A tangent bound for the logarithm turns an atom-size bound into an entropy bound. -/
theorem solution {W : Type*} [Fintype W]
    (p : W → ℝ) (a b : ℝ) (ha : 0 < a) (hp : ∀ w, 0 ≤ p w)
    (hmass : ∑ w, p w = 1) (hbound : ∀ w, p w ≤ b) :
    Real.log a + 1 - a * b ≤ entropy p := by
  have hterm (w : W) : p w * (Real.log a + 1 - a * b) ≤
      Real.negMulLog (p w) := by
    by_cases hz : p w = 0
    · simp [hz]
    · have hpos := lt_of_le_of_ne (hp w) (Ne.symm hz)
      have hlog := Real.log_le_sub_one_of_pos (mul_pos ha hpos)
      rw [Real.log_mul ha.ne' hpos.ne'] at hlog
      have hmul := mul_le_mul_of_nonneg_left hlog (hp w)
      have hb := mul_le_mul_of_nonneg_left (hbound w) (mul_nonneg ha.le (hp w))
      rw [Real.negMulLog_def]
      nlinarith
  have h := Finset.sum_le_sum (fun w (_ : w ∈ Finset.univ) => hterm w)
  simpa [entropy, ← Finset.sum_mul, hmass] using h

private theorem mass_entropy_lower {W : Type*} [Fintype W]
    (x : W → ℝ) (s a b : ℝ) (hs : 0 < s) (ha : 0 < a) (hx : ∀ w, 0 ≤ x w)
    (hmass : ∑ w, x w = s) (hbound : ∀ w, x w ≤ b * s) :
    s * (Real.log a + 1 - a * b) ≤ massEntropy x := by
  rw [(mme_regional_mass_entropy_algebra (C := Unit) (W := W)).2.1 x
    (by rw [hmass]; exact hs.ne'), hmass]
  apply mul_le_mul_of_nonneg_left _ hs.le
  apply solution _ _ _ ha
  · intro w; exact div_nonneg (hx w) hs.le
  · rw [← Finset.sum_div, hmass, div_self hs.ne']
  · intro w; exact (div_le_iff₀ hs).2 (hbound w)

private abbrev Split116 := Split 4 ![1, 1, 6]
private def c004 : Split116 := ⟨![0, 0, 4], by decide⟩
private def c013 : Split116 := ⟨![0, 1, 3], by decide⟩
private def c103 : Split116 := ⟨![1, 0, 3], by decide⟩
private def c112 : Split116 := ⟨![1, 1, 2], by decide⟩

private theorem split_univ : (Finset.univ : Finset Split116) = {c004, c013, c103, c112} := by
  decide

private def xCounts (r : Fin 6) (j : Fin 5) : ℕ :=
  if j = 0 then Released116.splitCount r c004 + Released116.splitCount r c013
  else if j = 1 then Released116.splitCount r c103 + Released116.splitCount r c112
  else 0

private theorem x_counts_bound : ∀ (r : Fin 6) (j : Fin 5),
    1000000 * xCounts r j ≤ 500001 * Released116.regionalSize r := by
  decide +kernel

private theorem x_counts_mass : ∀ r : Fin 6,
    ∑ j : Fin 5, xCounts r j = Released116.regionalSize r := by
  decide +kernel

private theorem x_counts_eq (r : Fin 6) (j : Fin 5) :
    marginalCounts Released116.splitCount 0 r j = xCounts r j := by
  classical
  unfold marginalCounts
  change (∑ c : {c : Split116 // c.val 0 = j}, Released116.splitCount r c.val) = _
  rw [← Finset.sum_subtype (Finset.univ.filter (fun c : Split116 => c.val 0 = j))
    (fun c => by simp) (Released116.splitCount r), Finset.sum_filter, split_univ]
  fin_cases j <;> norm_num [c004, c013, c103, c112, xCounts, add_assoc]

/-- The released X-coordinate entropy is at least 0.69 per parent occurrence.
The proof uses exact integer histogram bounds and the elementary logarithm inequality. -/
private theorem mme_released_116_coarse_rate_lower :
    (69 / 100 : ℝ) * ((∑ r : Fin 6, Released116.regionalSize r : ℕ) : ℝ) ≤
      coarsePotential Released116.splitCount 0 := by
  unfold coarsePotential
  simp only [x_counts_eq]
  have hr (r : Fin 6) :
      (Released116.regionalSize r : ℝ) * (Real.log 2 + 1 - 2 * (500001 / 1000000 : ℝ)) ≤
        massEntropy (fun j => (xCounts r j : ℝ)) := by
    apply mass_entropy_lower
    · exact_mod_cast (mme_released_116_regional_split_mass r).1
    · norm_num
    · intro j; exact Nat.cast_nonneg _
    · exact_mod_cast x_counts_mass r
    · intro j
      have h : (1000000 : ℝ) * xCounts r j ≤ 500001 * Released116.regionalSize r := by
        exact_mod_cast x_counts_bound r j
      linarith
  have h := Finset.sum_le_sum (fun r (_ : r ∈ Finset.univ) => hr r)
  rw [← Finset.sum_mul, ← Nat.cast_sum] at h
  have hlog : (69 / 100 : ℝ) ≤ Real.log 2 + 1 - 2 * (500001 / 1000000 : ℝ) := by
    have := Real.log_two_gt_d9
    linarith
  rw [mul_comm]
  exact (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)).trans h


#print axioms solution
