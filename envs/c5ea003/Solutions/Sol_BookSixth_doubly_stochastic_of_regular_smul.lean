-- Prove2me | solution 1 for BookSixth.doubly_stochastic_of_regular_smul
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T01:57:10.145348+00:00
-- url     : https://prove2.me/submissions/c39ccf0a-3cb9-4468-bbe3-10401a424946

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

theorem solution (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (c : ℝ)
    (hc : c ≠ 0) (hnn : ∀ i j, 0 ≤ M i j)
    (hrow : ∀ i, ∑ j, M i j = c) (hcol : ∀ j, ∑ i, M i j = c) :
    (∀ i j, 0 ≤ (c⁻¹ • M) i j) ∧ (∀ i, ∑ j, (c⁻¹ • M) i j = 1) ∧ (∀ j, ∑ i, (c⁻¹ • M) i j = 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    have hc0 : 0 ≤ c := by
      rw [← hrow i]
      exact Finset.sum_nonneg (fun j _ => hnn i j)
    simp only [Matrix.smul_apply, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr hc0) (hnn i j)
  · intro i
    simp only [Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum, hrow i]
    exact inv_mul_cancel₀ hc
  · intro j
    simp only [Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum, hcol j]
    exact inv_mul_cancel₀ hc
