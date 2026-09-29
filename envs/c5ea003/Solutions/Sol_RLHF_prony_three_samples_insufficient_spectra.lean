-- Prove2me | solution 1 for RLHF.prony_three_samples_insufficient_spectra
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T14:18:20.22785+00:00
-- url     : https://prove2.me/submissions/842254ce-4e9d-4224-a327-dfe3db98f75f

import Mathlib
import Definitions.Def_NumberTheory_RLHFGibbsVariational
import Definitions.Def_NumberTheory_RLHFPronySampling
import Definitions.Def_NumberTheory_RLHFSpectralRigidity
open RLHF in
theorem solution :
    ∃ r₁ p₁ r₂ p₂ : Bool → ℝ, IsPosDist p₁ ∧ IsPosDist p₂ ∧
      (∀ t ∈ ({0, 1, 2} : Set ℝ), partition t⁻¹ r₁ p₁ = partition t⁻¹ r₂ p₂) ∧
      rewardMass r₁ p₁ (Real.log 3) ≠ rewardMass r₂ p₂ (Real.log 3) := by
  -- `e^{r}` takes values `{3, 1}` w.p. `1/2, 1/2`, versus `{4, 3/2}` w.p. `1/5, 4/5`:
  -- both have mean `2` and second moment `5`, but only the first puts mass on `log 3`
  have e1 : ∀ x : ℝ, 0 < x → Real.exp (Real.log x / (1 : ℝ)⁻¹) = x := by
    intro x hx
    rw [inv_one, div_one, Real.exp_log hx]
  have e2 : ∀ x : ℝ, 0 < x → Real.exp (Real.log x / (2 : ℝ)⁻¹) = x ^ 2 := by
    intro x hx
    rw [div_inv_eq_mul, show Real.log x * 2 = Real.log (x ^ 2) by rw [Real.log_pow]; push_cast; ring,
      Real.exp_log (by positivity)]
  refine ⟨fun b => if b then Real.log 3 else 0, fun _ => 1 / 2,
    fun b => if b then Real.log 4 else Real.log (3 / 2), fun b => if b then 1 / 5 else 4 / 5,
    ⟨fun _ => by norm_num, by simp only [Fintype.sum_bool]; norm_num⟩,
    ⟨fun b => by cases b <;> norm_num, by simp only [Fintype.sum_bool]; norm_num⟩, ?_, ?_⟩
  · intro t ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    unfold partition
    simp only [Fintype.sum_bool, if_true, Bool.false_eq_true, if_false]
    rcases ht with rfl | rfl | rfl
    · simp only [inv_zero, div_zero, Real.exp_zero, mul_one]
      norm_num
    · rw [e1 3 (by norm_num), e1 4 (by norm_num), e1 (3 / 2) (by norm_num), inv_one, div_one,
        Real.exp_zero]
      norm_num
    · rw [e2 3 (by norm_num), e2 4 (by norm_num), e2 (3 / 2) (by norm_num), zero_div,
        Real.exp_zero]
      norm_num
  · have h0 : (0 : ℝ) ≠ Real.log 3 := (Real.log_pos (by norm_num)).ne
    have h4 : Real.log 4 ≠ Real.log 3 :=
      (Real.log_lt_log (by norm_num) (by norm_num : (3 : ℝ) < 4)).ne'
    have h32 : Real.log (3 / 2) ≠ Real.log 3 :=
      (Real.log_lt_log (by norm_num) (by norm_num : (3 / 2 : ℝ) < 3)).ne
    unfold rewardMass
    rw [Finset.sum_filter, Finset.sum_filter, Fintype.sum_bool, Fintype.sum_bool]
    simp only [if_true, Bool.false_eq_true, if_false, h0, h4, h32]
    norm_num
