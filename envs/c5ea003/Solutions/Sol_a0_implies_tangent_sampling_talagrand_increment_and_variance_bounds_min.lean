-- Prove2me | solution 1 for a0_implies_tangent_sampling_talagrand_increment_and_variance_bounds_min
-- status  : ACCEPTED   (prove)
-- author  : @Minghui
-- created : 2026-06-24T20:03:03.090282+00:00
-- url     : https://prove2.me/submissions/a0571ffe-2336-42d9-96d0-2f1de6bcf76d

import Theorems.Thm_a0_implies_tangent_coordinate_frobenius_bound_min
import Theorems.Thm_tangent_sampling_talagrand_increment_bound_from_coordinate_bound_min
import Theorems.Thm_tangent_sampling_talagrand_variance_bound_from_coordinate_bound_min

open MatrixCompletion

theorem solution :
    ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
      (μ₀ : ℝ) (S : SVD M r),
      0 < n₁ → 0 < n₂ → 0 < r → 0 < m → m ≤ n₁ * n₂ →
      1 ≤ μ₀ → A0 S μ₀ →
      TangentSamplingTalagrandIncrementBound S
        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
        (2 * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) / (m : ℝ)) ∧
      TangentSamplingTalagrandVarianceBound S
        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
        (2 * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) / (m : ℝ)) := by
  intro n₁ n₂ r m M μ₀ S hn₁ hn₂ hr hm hmle hμ₀ hA0
  have hcoord :
      TangentCoordinateFrobeniusBound S
        (2 * μ₀ * (r : ℝ) / (min n₁ n₂ : ℝ)) :=
    a0_implies_tangent_coordinate_frobenius_bound_min S μ₀
      hn₁ hn₂ hr hμ₀ hA0
  constructor
  · exact
      tangent_sampling_talagrand_increment_bound_from_coordinate_bound_min
        n₁ n₂ r m M μ₀ S hn₁ hn₂ hr hm hmle hμ₀ hcoord
  · exact
      tangent_sampling_talagrand_variance_bound_from_coordinate_bound_min
        n₁ n₂ r m M μ₀ S hn₁ hn₂ hr hm hmle hμ₀ hcoord
