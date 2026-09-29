-- Prove2me | solution 1 for linear_neumann_diagonal_contribution_under_general_sample_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-30T15:40:15.799461+00:00
-- url     : https://prove2.me/submissions/e38c2280-451f-4f06-b232-1379735b0982

import Mathlib.Tactic
import Theorems.Thm_bernoulli_event_probability_mono
import Theorems.Thm_linear_neumann_diagonal_centered_contribution_under_general_sample_bound
import Theorems.Thm_linear_neumann_diagonal_contribution_bound_from_centered_and_mean_bounds
import Theorems.Thm_linear_neumann_diagonal_mean_contribution_under_general_sample_bound
import Theorems.Thm_sample_ratio_between_zero_and_one

open MatrixCompletion

/-!
Source: Candès--Recht 2008, PDF p. 26, equations (6.8)--(6.9), and PDF p. 27,
where the centered diagonal term is bounded by Theorem 6.3 and the mean term
by Lemma 6.4.

This bridge combines the two pieces of equation (6.9).  The centered part is a
high-probability event, while the mean part is deterministic; probability
monotonicity transfers the centered event to the full diagonal event.
-/
theorem solution :
    ∃ Cdiag cdiag : ℝ, 0 < Cdiag ∧ 0 < cdiag ∧
      ∀ C' : ℝ, Cdiag ≤ C' →
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
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              spectralNorm
                (linearNeumannDiagonalContribution Omega S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
                (1 : ℝ) / 16) ≥
          1 - cdiag * Real.rpow (↑(max n₁ n₂)) (-β) := by
  rcases linear_neumann_diagonal_centered_contribution_under_general_sample_bound with
    ⟨Ccenter, ccenter, hCcenter, hccenter, hCenter⟩
  rcases linear_neumann_diagonal_mean_contribution_under_general_sample_bound with
    ⟨Cmean, hCmean, hMean⟩
  let Cdiag : ℝ := max Ccenter Cmean
  refine ⟨Cdiag, ccenter, ?_, hccenter, ?_⟩
  · exact lt_of_lt_of_le hCcenter (le_max_left Ccenter Cmean)
  · intro C' hC' β hβ n₁ n₂ r m M μ₀ μ₁ S
      hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
    have hCcenter_le : Ccenter ≤ C' :=
      le_trans (le_max_left Ccenter Cmean) hC'
    have hCmean_le : Cmean ≤ C' :=
      le_trans (le_max_right Ccenter Cmean) hC'
    have hCenterProb :=
      hCenter C' hCcenter_le β hβ n₁ n₂ r m M μ₀ μ₁ S
        hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
    have hMeanBound :=
      hMean C' hCmean_le β hβ n₁ n₂ r m M μ₀ μ₁ S
        hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
    rcases sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm with
      ⟨hpNonneg, hpLeOne⟩
    have hMono :
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              spectralNorm
                (linearNeumannDiagonalCenteredContribution Omega S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
                (1 : ℝ) / 32) ≤
          bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              spectralNorm
                (linearNeumannDiagonalContribution Omega S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
                (1 : ℝ) / 16) := by
      refine bernoulli_event_probability_mono
        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) _ _
        hpNonneg hpLeOne ?_
      intro Omega hCenteredBound
      have hCenteredBound' :
          spectralNorm
              (linearNeumannDiagonalCenteredContribution Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
            ((1 : ℝ) / 32) * Real.rpow (1 : ℝ) (-1) := by
        simpa using hCenteredBound
      have hMeanBound' :
          spectralNorm
              (linearNeumannDiagonalMeanContribution S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
            ((1 : ℝ) / 32) * Real.rpow (1 : ℝ) (-1) := by
        simpa using hMeanBound
      have hDiag :=
        linear_neumann_diagonal_contribution_bound_from_centered_and_mean_bounds
          S Omega ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          ((1 : ℝ) / 32) ((1 : ℝ) / 32) 1
          hCenteredBound' hMeanBound'
      norm_num at hDiag ⊢
      exact hDiag
    exact le_trans hCenterProb hMono
