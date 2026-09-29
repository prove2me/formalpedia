-- Prove2me | solution 1 for strict_certificate_and_injectivity_increase_nuclear_norm_for_perturbation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-14T00:18:40.845683+00:00
-- url     : https://prove2.me/submissions/fa197d87-b329-40f6-b98b-b5700dee69b2

import Theorems.Thm_strict_certificate_and_injectivity_increase_nuclear_norm_for_perturbation
import Theorems.Thm_strict_dual_certificate_normal_component_nonzero_gives_nuclear_norm_gap
import Theorems.Thm_normal_projection_zero_and_restricted_sampling_injective_forces_zero

open MatrixCompletion

/-- Split the perturbation proof by whether the normal component vanishes. -/
theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (Omega : Finset (Fin n₁ × Fin n₂))
    (Y H : Matrix (Fin n₁) (Fin n₂) ℝ) :
    SamplingOperatorInjectiveOnT Omega S →
    StrictDualCertificate Omega S Y →
    samplingProjection Omega H = 0 →
    H ≠ 0 →
    nuclearNorm M < nuclearNorm (M + H) := by
  intro hInjective hCertificate hSample hNonzero
  by_cases hNormal : normalProjection S H = 0
  · have hHzero :=
      normal_projection_zero_and_restricted_sampling_injective_forces_zero
        S Omega H hInjective hSample hNormal
    exact False.elim (hNonzero hHzero)
  · exact strict_dual_certificate_normal_component_nonzero_gives_nuclear_norm_gap
      S Omega Y H hCertificate hSample hNormal

