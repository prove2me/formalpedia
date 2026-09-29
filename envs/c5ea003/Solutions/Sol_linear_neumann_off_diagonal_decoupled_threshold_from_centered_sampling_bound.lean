-- Prove2me | solution 1 for linear_neumann_off_diagonal_decoupled_threshold_from_centered_sampling_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T07:49:46.326511+00:00
-- url     : https://prove2.me/submissions/2f3f41ff-9a83-48c8-bf5c-d9397f4a825b

import Definitions.Def_matrix_completion_neumann
import Theorems.Thm_centered_sampling_fluctuation_linear_neumann_threshold_from_entry_scale

open MatrixCompletion

/-- Specialize the generic linear centered-fluctuation threshold to the
off-diagonal decoupled Neumann coefficient matrix. -/
theorem solution
    (Cfixed : ℝ) :
    0 < Cfixed →
    ∃ Cthreshold : ℝ, 0 < Cthreshold ∧
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
        ∀ Ccoef : ℝ, 0 < Ccoef →
        ∀ Omega1 Omega2 : Finset (Fin n₁ × Fin n₂),
        LinearNeumannOffDiagonalCoefficientBound Omega2 S
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (Ccoef * μ₁ *
              Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                Real.sqrt
                  ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
                      (β * Real.log (↑(max n₁ n₂)))) / (m : ℝ))) →
        linearNeumannOffDiagonalDecoupledContribution Omega1 Omega2 S
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) =
          centeredSamplingFluctuation Omega1
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (linearNeumannOffDiagonalCoefficientMatrix Omega2 S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) →
        CenteredSamplingSpectralBound Omega1
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (linearNeumannOffDiagonalCoefficientMatrix Omega2 S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))
            (Cfixed * Real.sqrt
              ((β * (↑(max n₁ n₂)) *
                  Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              entrySupNorm
                (linearNeumannOffDiagonalCoefficientMatrix Omega2 S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))) →
        spectralNorm
            (linearNeumannOffDiagonalDecoupledContribution
              Omega1 Omega2 S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
          (Cthreshold * Ccoef) * Real.rpow lam (-1) := by
  intro hCfixed
  rcases
      centered_sampling_fluctuation_linear_neumann_threshold_from_entry_scale
        Cfixed hCfixed with
    ⟨Cthreshold, hCthreshold, hThreshold⟩
  refine ⟨Cthreshold, hCthreshold, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
    Ccoef hCcoef Omega1 Omega2 hCoef hRep hCentered
  exact hThreshold β lam hβ hlam n₁ n₂ r m μ₀ μ₁
    hn₁ hn₂ hr hm hμ₀ hμ₁ hmLower Ccoef hCcoef Omega1
    (linearNeumannOffDiagonalCoefficientMatrix Omega2 S
      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))
    (linearNeumannOffDiagonalDecoupledContribution Omega1 Omega2 S
      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))
    hRep hCoef hCentered
