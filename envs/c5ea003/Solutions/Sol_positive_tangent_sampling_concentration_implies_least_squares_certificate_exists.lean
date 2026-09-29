-- Prove2me | solution 1 for positive_tangent_sampling_concentration_implies_least_squares_certificate_exists
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-14T22:19:00.059933+00:00
-- url     : https://prove2.me/submissions/5de0dc7c-4b4f-43dd-af3b-a189cb5b8aa5

import Theorems.Thm_positive_tangent_sampling_concentration_implies_least_squares_certificate_exists
import Theorems.Thm_tangent_sampling_concentration_implies_tangent_sampling_surjective_on_tangent
import Theorems.Thm_sign_matrix_mem_tangent_space
import Theorems.Thm_tangent_sampling_surjectivity_gives_supported_tangent_certificate
import Theorems.Thm_supported_tangent_certificate_set_has_frobenius_minimizer

open MatrixCompletion

/-- Build a supported tangent certificate from surjectivity, then choose the
Frobenius-minimal one. -/
theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ) :
    0 < p →
    TangentSamplingConcentration Omega S p ((1 : ℝ) / 2) →
    ∃ Y : Matrix (Fin n₁) (Fin n₂) ℝ, LeastSquaresDualCertificate Omega S Y := by
  intro hp hConcentration
  have hSurjective :=
    tangent_sampling_concentration_implies_tangent_sampling_surjective_on_tangent
      Omega S p hp hConcentration
  have hSign := sign_matrix_mem_tangent_space S
  have hSupported :=
    tangent_sampling_surjectivity_gives_supported_tangent_certificate
      S Omega hSurjective hSign
  exact supported_tangent_certificate_set_has_frobenius_minimizer S Omega hSupported

