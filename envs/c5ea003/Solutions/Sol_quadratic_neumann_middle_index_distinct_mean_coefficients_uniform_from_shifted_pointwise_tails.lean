-- Prove2me | solution 1 for quadratic_neumann_middle_index_distinct_mean_coefficients_uniform_from_shifted_pointwise_tails
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T23:23:08.051643+00:00
-- url     : https://prove2.me/submissions/2ac67b56-0e14-41df-aa15-920e69e1f4c5

import Definitions.Def_matrix_completion_neumann
import Theorems.Thm_bernoulli_uniform_bound_over_matrix_indices_from_shifted_pointwise_tails
import Theorems.Thm_sample_ratio_between_zero_and_one

open MatrixCompletion

/-!
Source: Candes-Recht 2008, PDF p. 29, the union-bound step after equation
(6.17), and PDF p. 30, equation (6.20), where the `ω₁ = ω₃ ≠ ω₂` mean
coefficient is controlled uniformly over coordinate indices.  This repairs the
old no-loss uniformization node by asking pointwise tails at exponent `β + 2`,
which pays for the `n₁ n₂ ≤ n²` coordinate union bound.
-/

theorem solution
    (Cpoint cpoint : ℝ) :
    0 < Cpoint → 0 < cpoint →
    ∃ Ccoef ccoef : ℝ, 0 < Ccoef ∧ 0 < ccoef ∧
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
        (∀ w1 : Fin n₁ × Fin n₂,
          bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega =>
                |quadraticMiddleIndexDistinctMeanCoefficient Omega S
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1| ≤
                  Cpoint *
                    Real.sqrt (β * Real.log (↑(max n₁ n₂))) *
                      Real.rpow
                        ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ)) / (m : ℝ))
                        ((3 : ℝ) / 2)) ≥
            1 - cpoint * Real.rpow (↑(max n₁ n₂)) (-(β + 2))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              QuadraticMiddleIndexDistinctMeanCoefficientBound Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (Ccoef *
                  Real.sqrt (β * Real.log (↑(max n₁ n₂))) *
                    Real.rpow
                      ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ)) / (m : ℝ))
                      ((3 : ℝ) / 2))) ≥
          1 - ccoef * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hCpoint hcpoint
  rcases bernoulli_uniform_bound_over_matrix_indices_from_shifted_pointwise_tails
      Cpoint cpoint hCpoint hcpoint with
    ⟨Ccoef, ccoef, hCcoef, hccoef, hUniform⟩
  refine ⟨Ccoef, ccoef, hCcoef, hccoef, ?_⟩
  intro β lam hβ _hlam n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ _hr hm _hμ₀ _hμ₁ _hA0 _hA1 _hmLower hPointwise
  rcases sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm with
    ⟨hp_nonneg, hp_le_one⟩
  let scale : ℝ :=
    Real.sqrt (β * Real.log (↑(max n₁ n₂))) *
      Real.rpow ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ)) / (m : ℝ))
        ((3 : ℝ) / 2)
  have hPointwise' :
      ∀ w1 : Fin n₁ × Fin n₂,
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              |quadraticMiddleIndexDistinctMeanCoefficient Omega S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1| ≤
                Cpoint * scale) ≥
          1 - cpoint * Real.rpow (↑(max n₁ n₂)) (-(β + 2)) := by
    intro w1
    simpa [scale, mul_assoc] using hPointwise w1
  have h :=
    hUniform β ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) scale hβ
      hp_nonneg hp_le_one n₁ n₂ hn₁ hn₂
      (fun w1 Omega =>
        quadraticMiddleIndexDistinctMeanCoefficient Omega S
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1)
      hPointwise'
  simpa [QuadraticMiddleIndexDistinctMeanCoefficientBound, scale, mul_assoc] using h
