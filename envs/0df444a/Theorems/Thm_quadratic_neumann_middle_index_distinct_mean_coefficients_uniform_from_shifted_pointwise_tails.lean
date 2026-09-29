-- Prove2me | Theorems.Thm_quadratic_neumann_middle_index_distinct_mean_coefficients_uniform_from_shifted_pointwise_tails
-- name    : quadratic_neumann_middle_index_distinct_mean_coefficients_uniform_from_shifted_pointwise_tails
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-21T23:23:06.902017+00:00
-- url     : https://prove2.me/theorems/a701e002-8919-4759-9df1-c75be76265cc
-- statement:
--   This is the corrected coordinate-uniformization step for the mean coefficients in the $\omega_1=\omega_3\ne\omega_2$ quadratic Neumann contribution.
--
--   For each outer coordinate $w_1$, assume the scalar pointwise tail
--   $$
--   \mathbb P\left\{|H_{w_1}(\Omega)|\le C_{\rm point}\sqrt{\beta\log n}\left({\mu_0nr\over m}\right)^{3/2}\right\}
--   \ge 1-c_{\rm point}n^{-(\beta+2)},\qquad n=\max(n_1,n_2).
--   $$
--   Then, after union bounding over the $n_1n_2$ possible coordinates, the uniform coefficient event satisfies
--   $$
--   \mathbb P\left\{\forall w_1,\ |H_{w_1}(\Omega)|\le C_{\rm coef}\sqrt{\beta\log n}\left({\mu_0nr\over m}\right)^{3/2}\right\}
--   \ge 1-c_{\rm coef}n^{-\beta}.
--   $$
--   The two-power shift in the pointwise exponent pays for the coordinate cardinality loss.
--
--   Source: Candes-Recht 2008, PDF p. 29 after equation (6.17), and PDF p. 30 equation (6.20), where the repeated-index quadratic terms are separated into coordinate coefficient events.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_middle_index_distinct_mean_coefficients_uniform_from_shifted_pointwise_tails
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
  sorry
