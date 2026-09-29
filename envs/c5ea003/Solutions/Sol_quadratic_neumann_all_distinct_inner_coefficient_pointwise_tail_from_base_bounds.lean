-- Prove2me | solution 1 for quadratic_neumann_all_distinct_inner_coefficient_pointwise_tail_from_base_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T07:49:51.625691+00:00
-- url     : https://prove2.me/submissions/761b695f-145d-4abf-b76f-f4b695f691ad

import Theorems.Thm_scalar_centered_sampling_bernstein_lambda_half_tail_from_quadratic_base_bounds

open MatrixCompletion

/-- Specialize the generic scalar Bernstein `λ^{-1/2}` estimate to the inner
`G_{ω₂}` coefficient in the all-distinct quadratic term. -/
theorem solution
    (Centry Cfro : ℝ) :
    0 < Centry → 0 < Cfro →
    ∃ Cpoint cpoint : ℝ, 0 < Cpoint ∧ 0 < cpoint ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
            (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              (β * Real.log (↑(max n₁ n₂))) →
        ∀ w1 w2 : Fin n₁ × Fin n₂,
        (∀ Omega3 : Finset (Fin n₁ × Fin n₂),
          quadraticAllDistinctInnerCoefficient Omega3 S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1 w2 =
            matrixEntrySum
              (centeredSamplingFluctuation Omega3
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (quadraticAllDistinctInnerBaseMatrix S w1 w2))) →
        entrySupNorm (quadraticAllDistinctInnerBaseMatrix S w1 w2) ≤
          Centry * μ₀ ^ 2 *
            (((r : ℝ) / (↑(max n₁ n₂))) ^ 2) →
        frobeniusNorm (quadraticAllDistinctInnerBaseMatrix S w1 w2) ≤
          Cfro * Real.rpow μ₀ ((3 : ℝ) / 2) *
            Real.rpow ((r : ℝ) / (↑(max n₁ n₂))) ((3 : ℝ) / 2) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega3 =>
              |quadraticAllDistinctInnerCoefficient Omega3 S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1 w2| ≤
                Cpoint * Real.rpow lam (-((1 : ℝ) / 2))) ≥
          1 - cpoint * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hCentry hCfro
  rcases
      scalar_centered_sampling_bernstein_lambda_half_tail_from_quadratic_base_bounds
        Centry Cfro hCentry hCfro with
    ⟨Cpoint, cpoint, hCpoint, hcpoint, hScalar⟩
  refine ⟨Cpoint, cpoint, hCpoint, hcpoint, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
    w1 w2 hRep hEntry hFrob
  exact hScalar β lam hβ hlam n₁ n₂ r m μ₀
    hn₁ hn₂ hr hm hμ₀ hmLower
    (fun Omega3 =>
      quadraticAllDistinctInnerCoefficient Omega3 S
        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1 w2)
    (quadraticAllDistinctInnerBaseMatrix S w1 w2)
    hRep hEntry hFrob

