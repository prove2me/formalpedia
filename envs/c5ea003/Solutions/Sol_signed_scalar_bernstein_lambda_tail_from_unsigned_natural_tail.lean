-- Prove2me | solution 1 for signed_scalar_bernstein_lambda_tail_from_unsigned_natural_tail
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-14T05:26:12.297656+00:00
-- url     : https://prove2.me/submissions/21fa15e8-864d-4928-bb6b-e6b83ef210aa

import Theorems.Thm_signed_scalar_bernstein_lambda_tail_from_unsigned_natural_tail
import Theorems.Thm_signed_scalar_bernstein_lambda_event_from_unsigned_natural_event
import Theorems.Thm_bernoulli_event_probability_mono
import Theorems.Thm_sample_ratio_between_zero_and_one

open MatrixCompletion

/-- Convert the deterministic signed/unsigned event inclusion into the signed
scalar Bernstein probability bound by Bernoulli event monotonicity. -/
theorem solution
    (Cnatural cnatural Ccompat : ℝ) :
    0 < Cnatural → 0 < cnatural → 0 < Ccompat →
    ∃ Cpoint cpoint : ℝ, 0 < Cpoint ∧ 0 < cpoint ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (μ₀ sign : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ →
        |sign| *
            Real.sqrt (β * Real.log (↑(max n₁ n₂))) *
            Real.rpow
              ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ)) / (m : ℝ))
              ((3 : ℝ) / 2) ≤
          Ccompat * Real.rpow lam (-1) →
        ∀ (Coeff : Finset (Fin n₁ × Fin n₂) → ℝ)
          (B : Matrix (Fin n₁) (Fin n₂) ℝ),
        (∀ Omega : Finset (Fin n₁ × Fin n₂),
          Coeff Omega =
            sign *
              matrixEntrySum
                (centeredSamplingFluctuation Omega
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) B)) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              |matrixEntrySum
                (centeredSamplingFluctuation Omega
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) B)| ≤
                Cnatural *
                  Real.sqrt (β * Real.log (↑(max n₁ n₂))) *
                    Real.rpow
                      ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ)) / (m : ℝ))
                      ((3 : ℝ) / 2)) ≥
          1 - cnatural * Real.rpow (↑(max n₁ n₂)) (-β) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              |Coeff Omega| ≤ Cpoint * Real.rpow lam (-1)) ≥
          1 - cpoint * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hCnatural hcnatural hCcompat
  rcases signed_scalar_bernstein_lambda_event_from_unsigned_natural_event
      Cnatural Ccompat hCnatural hCcompat with
    ⟨Cpoint, hCpoint, hPoint⟩
  refine ⟨Cpoint, cnatural, hCpoint, hcnatural, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m μ₀ sign hn₁ hn₂ hr hm hμ₀
    hCompat Coeff B hCoeff hUnsignedProb
  have hp : 0 ≤ ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) ∧
      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) ≤ 1 := by
    exact sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm
  have hMono :
      bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (fun Omega =>
            |matrixEntrySum
              (centeredSamplingFluctuation Omega
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) B)| ≤
              Cnatural *
                Real.sqrt (β * Real.log (↑(max n₁ n₂))) *
                  Real.rpow
                    ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ)) / (m : ℝ))
                    ((3 : ℝ) / 2)) ≤
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (fun Omega =>
            |Coeff Omega| ≤ Cpoint * Real.rpow lam (-1)) := by
    refine bernoulli_event_probability_mono
      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) _ _ hp.1 hp.2 ?_
    intro Omega hUnsigned
    exact hPoint β lam hβ hlam n₁ n₂ r m μ₀ sign
      hn₁ hn₂ hr hm hμ₀ hCompat Coeff B hCoeff Omega hUnsigned
  exact le_trans hUnsignedProb hMono

