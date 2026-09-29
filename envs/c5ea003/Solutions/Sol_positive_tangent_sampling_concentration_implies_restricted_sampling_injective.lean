-- Prove2me | solution 1 for positive_tangent_sampling_concentration_implies_restricted_sampling_injective
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-14T22:19:00.14251+00:00
-- url     : https://prove2.me/submissions/17120a98-38c6-4973-86db-ad9ab11263ab

import Theorems.Thm_positive_tangent_sampling_concentration_implies_restricted_sampling_injective
import Theorems.Thm_tangent_sampling_concentration_controls_unsampled_tangent_frobenius_norm
import Theorems.Thm_frobenius_norm_zero_implies_matrix_zero

open MatrixCompletion

/-- Prove injectivity by showing every sampled-zero tangent vector has zero
Frobenius norm, hence is the zero matrix. -/
theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ) :
    0 < p →
    TangentSamplingConcentration Omega S p ((1 : ℝ) / 2) →
    SamplingOperatorInjectiveOnT Omega S := by
  intro hp hConcentration H hTangent hSample
  have hFrob :=
    tangent_sampling_concentration_controls_unsampled_tangent_frobenius_norm
      Omega S p H hp hConcentration hTangent hSample
  exact frobenius_norm_zero_implies_matrix_zero H hFrob

