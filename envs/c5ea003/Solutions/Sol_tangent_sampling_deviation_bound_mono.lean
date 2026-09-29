-- Prove2me | solution 1 for tangent_sampling_deviation_bound_mono
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-15T15:18:46.634981+00:00
-- url     : https://prove2.me/submissions/3d79fbef-a67b-4711-9c6a-b02b60a0a77c

import Theorems.Thm_tangent_sampling_deviation_bound_mono

open MatrixCompletion

theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r)
    (p small large : ℝ) :
    small ≤ large →
    TangentSamplingDeviationBound Omega S p small →
    TangentSamplingDeviationBound Omega S p large := by
  intro hle hsmall
  exact le_trans hsmall hle

