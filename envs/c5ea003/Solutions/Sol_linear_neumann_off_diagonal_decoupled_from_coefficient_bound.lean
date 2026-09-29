-- Prove2me | solution 1 for linear_neumann_off_diagonal_decoupled_from_coefficient_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T07:49:45.839599+00:00
-- url     : https://prove2.me/submissions/d5fbd34d-d279-41bb-a2e7-417e8b955044

import Theorems.Thm_linear_neumann_off_diagonal_outer_sampling_conditional_from_coefficient_bound
import Theorems.Thm_linear_neumann_off_diagonal_pair_probability_from_coefficient_and_outer_conditional_bound

open MatrixCompletion

/-- Split the final outer sampling step for the decoupled off-diagonal linear
Neumann term into a fixed-`Ω₂` conditional sampling estimate and a pair-product
probability lift. -/
theorem solution
    (Cfixed : ℝ) :
    0 < Cfixed →
    ∃ Couter couter : ℝ, 0 < Couter ∧ 0 < couter ∧
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
        (∀ X : Matrix (Fin n₁) (Fin n₂) ℝ,
          bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega1 =>
                CenteredSamplingSpectralBound Omega1
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X
                  (Cfixed * Real.sqrt
                    ((β * (↑(max n₁ n₂)) *
                        Real.log (↑(max n₁ n₂))) /
                      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                    entrySupNorm X)) ≥
            1 - (1 : ℝ) * Real.rpow (↑(max n₁ n₂)) (-β)) →
        (∀ Omega1 Omega2 : Finset (Fin n₁ × Fin n₂),
          linearNeumannOffDiagonalDecoupledContribution Omega1 Omega2 S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) =
            centeredSamplingFluctuation Omega1
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (linearNeumannOffDiagonalCoefficientMatrix Omega2 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))) →
        ∀ Ccoef ccoef : ℝ, 0 < Ccoef → 0 < ccoef →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega2 =>
              LinearNeumannOffDiagonalCoefficientBound Omega2 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (Ccoef * μ₁ *
                  Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                    Real.sqrt
                      ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
                          (β * Real.log (↑(max n₁ n₂)))) / (m : ℝ)))) ≥
          1 - ccoef * Real.rpow (↑(max n₁ n₂)) (-β) →
        bernoulliPairEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega1 Omega2 =>
              spectralNorm
                (linearNeumannOffDiagonalDecoupledContribution
                  Omega1 Omega2 S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
                (Couter * Ccoef) * Real.rpow lam (-1)) ≥
          1 - (couter + ccoef) *
            Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hCfixed
  rcases linear_neumann_off_diagonal_outer_sampling_conditional_from_coefficient_bound
      Cfixed hCfixed with
    ⟨Ccond, ccond, hCcond, hccond, hConditional⟩
  rcases linear_neumann_off_diagonal_pair_probability_from_coefficient_and_outer_conditional_bound
      Ccond ccond hCcond hccond with
    ⟨Couter, couter, hCouter, hcouter, hPair⟩
  refine ⟨Couter, couter, hCouter, hcouter, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
    hFixedAll hRep Ccoef ccoef hCcoef hccoef hCoefProb
  have hCondProb :
      ∀ Omega2 : Finset (Fin n₁ × Fin n₂),
        LinearNeumannOffDiagonalCoefficientBound Omega2 S
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (Ccoef * μ₁ *
              Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                Real.sqrt
                  ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
                      (β * Real.log (↑(max n₁ n₂)))) / (m : ℝ))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega1 =>
              spectralNorm
                (linearNeumannOffDiagonalDecoupledContribution
                  Omega1 Omega2 S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
                (Ccond * Ccoef) * Real.rpow lam (-1)) ≥
          1 - ccond * Real.rpow (↑(max n₁ n₂)) (-β) := by
    intro Omega2 hCoefEvent
    have hRepFixed :
        ∀ Omega1 : Finset (Fin n₁ × Fin n₂),
          linearNeumannOffDiagonalDecoupledContribution Omega1 Omega2 S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) =
            centeredSamplingFluctuation Omega1
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (linearNeumannOffDiagonalCoefficientMatrix Omega2 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) := by
      intro Omega1
      exact hRep Omega1 Omega2
    exact hConditional β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
      hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower hFixedAll
      Ccoef hCcoef Omega2 hCoefEvent hRepFixed
  exact hPair β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
    Ccoef ccoef hCcoef hccoef hCoefProb hCondProb

