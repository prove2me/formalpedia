-- Prove2me | solution 1 for normal_projection_zero_and_restricted_sampling_injective_forces_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-14T00:40:37.077426+00:00
-- url     : https://prove2.me/submissions/8d0633e8-b472-4195-907e-893e38087de4

import Theorems.Thm_normal_projection_zero_and_restricted_sampling_injective_forces_zero
import Theorems.Thm_normal_projection_zero_implies_tangent_projection_eq_self

open MatrixCompletion

/-- Convert `P_{T^\perp} H = 0` into `H ∈ T`, then apply injectivity of the
sampling operator restricted to the tangent space. -/
theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (Omega : Finset (Fin n₁ × Fin n₂))
    (H : Matrix (Fin n₁) (Fin n₂) ℝ) :
    SamplingOperatorInjectiveOnT Omega S →
    samplingProjection Omega H = 0 →
    normalProjection S H = 0 →
    H = 0 := by
  intro hInjective hSample hNormalZero
  have hTangent :=
    normal_projection_zero_implies_tangent_projection_eq_self S H hNormalZero
  exact hInjective H hTangent hSample

