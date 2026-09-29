-- Prove2me | solution 1 for centered_sampling_coefficient_subgaussian_mgf
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-22T00:24:54.439447+00:00
-- url     : https://prove2.me/submissions/e54ed891-858d-4954-a2fe-2fcb50b7102f

import Definitions.Def_matrix_completion_neumann
import Definitions.Def_matrix_completion_tangent
import Theorems.Thm_centered_sampling_coefficient_mgf_factorization
import Theorems.Thm_two_point_hoeffding_mgf_bound
import Mathlib.Analysis.SpecialFunctions.Exp

open MatrixCompletion
open scoped BigOperators Classical

set_option maxHeartbeats 1000000

/-- **Sub-Gaussian MGF bound** for the centered-sampling coefficient statistic.
`E[exp(λ·Coeff)] ≤ exp(λ²·‖B‖_F² / (8 p²))` for `0 < p ≤ 1`. -/
theorem solution {n₁ n₂ : ℕ} (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (B : Matrix (Fin n₁) (Fin n₂) ℝ) (lam : ℝ) :
    bernoulliExpectation p
        (fun Omega =>
          Real.exp (lam * matrixEntrySum (centeredSamplingFluctuation Omega p B))) ≤
      Real.exp (lam ^ 2 * frobeniusNormSq B / (8 * p ^ 2)) := by
  classical
  -- Step 1: rewrite the LHS as the product of per-coordinate MGFs.
  rw [centered_sampling_coefficient_mgf_factorization p B lam]
  -- Step 2: bound each factor by exp(λ² B_w² / (8 p²)) using two-point Hoeffding.
  have hpne : p ≠ 0 := ne_of_gt hp0
  have hfac : ∀ w : Fin n₁ × Fin n₂,
      (p * Real.exp (lam * (p⁻¹ * (B w.1 w.2) * (1 - p)))
        + (1 - p) * Real.exp (lam * (p⁻¹ * (B w.1 w.2) * (0 - p)))) ≤
      Real.exp (lam ^ 2 * (B w.1 w.2) ^ 2 / (8 * p ^ 2)) := by
    intro w
    set a := lam * (p⁻¹ * (B w.1 w.2) * (1 - p)) with ha
    set b := lam * (p⁻¹ * (B w.1 w.2) * (0 - p)) with hb
    have hH := two_point_hoeffding_mgf_bound p a b (le_of_lt hp0) hp1
    refine hH.trans ?_
    apply Real.exp_le_exp.mpr
    -- p*a + (1-p)*b = 0  and  (a-b)²/8 = λ² B_w² /(8 p²).
    have hmean : p * a + (1 - p) * b = 0 := by
      rw [ha, hb]; field_simp; ring
    have hrange : (a - b) ^ 2 / 8 = lam ^ 2 * (B w.1 w.2) ^ 2 / (8 * p ^ 2) := by
      rw [ha, hb]
      rw [div_eq_div_iff (by norm_num) (by positivity)]
      field_simp
      ring
    rw [hmean, hrange, zero_add]
  -- Step 3: product of bounds is exp of the sum.
  calc ∏ w : Fin n₁ × Fin n₂,
        (p * Real.exp (lam * (p⁻¹ * (B w.1 w.2) * (1 - p)))
          + (1 - p) * Real.exp (lam * (p⁻¹ * (B w.1 w.2) * (0 - p))))
      ≤ ∏ w : Fin n₁ × Fin n₂, Real.exp (lam ^ 2 * (B w.1 w.2) ^ 2 / (8 * p ^ 2)) := by
        apply Finset.prod_le_prod
        · intro w _
          have h1p : (0:ℝ) ≤ 1 - p := by linarith
          have := mul_nonneg (le_of_lt hp0) (Real.exp_pos (lam * (p⁻¹ * (B w.1 w.2) * (1 - p)))).le
          have := mul_nonneg h1p (Real.exp_pos (lam * (p⁻¹ * (B w.1 w.2) * (0 - p)))).le
          linarith
        · intro w _; exact hfac w
    _ = Real.exp (∑ w : Fin n₁ × Fin n₂, lam ^ 2 * (B w.1 w.2) ^ 2 / (8 * p ^ 2)) := by
        rw [← Real.exp_sum]
    _ = Real.exp (lam ^ 2 * frobeniusNormSq B / (8 * p ^ 2)) := by
        congr 1
        rw [frobeniusNormSq, ← Fintype.sum_prod_type']
        rw [Finset.mul_sum, Finset.sum_div]
