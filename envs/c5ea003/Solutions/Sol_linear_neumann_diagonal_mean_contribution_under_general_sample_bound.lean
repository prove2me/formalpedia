-- Prove2me | solution 1 for linear_neumann_diagonal_mean_contribution_under_general_sample_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-30T15:38:50.173123+00:00
-- url     : https://prove2.me/submissions/a40315d8-3267-4593-abe6-271ee5d044bc

import Mathlib.Tactic
import Theorems.Thm_linear_neumann_correction_lambda_bound_le_one_eighth
import Theorems.Thm_linear_neumann_correction_lambda_sample_bound_from_general_bound
import Theorems.Thm_linear_neumann_diagonal_mean_contribution_small_with_lambda

open MatrixCompletion

/-!
Source: Candès--Recht 2008, PDF p. 6, Theorem 1.3/equation (1.9), PDF p. 26,
equation (6.9), and PDF p. 27, Lemma 6.4/equations (6.10)--(6.11).

This is a formal bridge from the already proved lambda-form deterministic mean
estimate to the full Theorem 1.3 sample regime.  We choose a fixed large lambda
so that the mean threshold is at most `1/32`.
-/
theorem solution :
    ∃ Cmean : ℝ, 0 < Cmean ∧
      ∀ C' : ℝ, Cmean ≤ C' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          C' * max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                  (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4))
            * (↑(max n₁ n₂)) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂))) →
        spectralNorm
            (linearNeumannDiagonalMeanContribution S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
          (1 : ℝ) / 32 := by
  rcases linear_neumann_diagonal_mean_contribution_small_with_lambda with
    ⟨Cmean₀, hCmean₀, hMean⟩
  have hFourCmean₀ : 0 < 4 * Cmean₀ := by positivity
  rcases linear_neumann_correction_lambda_sample_bound_from_general_bound
      (4 * Cmean₀) with
    ⟨Csample, hCsample, hSample⟩
  refine ⟨Csample, hCsample, ?_⟩
  intro C' hC' β hβ n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
  let lam : ℝ := max 1 (8 * (4 * Cmean₀))
  have hlam : 1 ≤ lam := by
    dsimp [lam]
    exact le_max_left _ _
  have hLambdaSample :=
    hSample C' hC' β hβ n₁ n₂ r m M μ₀ μ₁ S
      hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
  have hMeanBound :=
    hMean β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
      hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hLambdaSample
  have hFourSmall :
      (4 * Cmean₀) * Real.rpow lam (-1) ≤ (1 : ℝ) / 8 := by
    dsimp [lam]
    exact linear_neumann_correction_lambda_bound_le_one_eighth
      (4 * Cmean₀) hFourCmean₀
  have hSmall :
      Cmean₀ * Real.rpow lam (-1) ≤ (1 : ℝ) / 32 := by
    nlinarith
  exact le_trans hMeanBound hSmall
