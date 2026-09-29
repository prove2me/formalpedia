-- Prove2me | solution 1 for linear_neumann_off_diagonal_contribution_small_with_lambda
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T04:25:33.573302+00:00
-- url     : https://prove2.me/submissions/ce7e7ef7-9f01-4310-963a-81d51f0b1b6a

import Theorems.Thm_linear_neumann_off_diagonal_decoupled_contribution_small_with_lambda
import Theorems.Thm_linear_neumann_off_diagonal_decoupling_transfer
import Theorems.Thm_sample_ratio_between_zero_and_one

open MatrixCompletion

/-- Prove the off-diagonal first Neumann estimate by the paper's decoupling
step: bound the two-copy model, then transfer back to the original model. -/
theorem solution :
    ∃ Coff coff : ℝ, 0 < Coff ∧ 0 < coff ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          lam * μ₁ * max (Real.sqrt μ₀) μ₁ *
            (↑(max n₁ n₂)) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              spectralNorm
                (linearNeumannOffDiagonalContribution Omega S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
                Coff * Real.rpow lam (-1)) ≥
          1 - coff * Real.rpow (↑(max n₁ n₂)) (-β) := by
  rcases linear_neumann_off_diagonal_decoupled_contribution_small_with_lambda with
    ⟨Cdec, cdec, hCdec, hcdec, hDecoupled⟩
  rcases linear_neumann_off_diagonal_decoupling_transfer with
    ⟨Cmul, cmul, hCmul, hcmul, hTransfer⟩
  refine ⟨Cmul * Cdec, cmul * cdec,
    mul_pos hCmul hCdec, mul_pos hcmul hcdec, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
  have hDecoupledProb :=
    hDecoupled β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
      hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
  rcases sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm with
    ⟨hpNonneg, hpLeOne⟩
  exact hTransfer S ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
    Cdec cdec β lam hpNonneg hpLeOne hCdec hcdec hDecoupledProb

