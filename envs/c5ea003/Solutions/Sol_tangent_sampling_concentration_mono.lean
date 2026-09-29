-- Prove2me | solution 1 for tangent_sampling_concentration_mono
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-15T15:18:47.056418+00:00
-- url     : https://prove2.me/submissions/608c55c6-d762-46f0-a37d-7fe63125c506

import Theorems.Thm_tangent_sampling_concentration_mono

open MatrixCompletion

theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r)
    (p small large : ℝ) :
    0 ≤ p →
    small ≤ large →
    TangentSamplingConcentration Omega S p small →
    TangentSamplingConcentration Omega S p large := by
  intro hp hle hconc X hX
  have hnorm : 0 ≤ frobeniusNorm X := by
    exact Real.sqrt_nonneg _
  have hscaled :
      small * p * frobeniusNorm X ≤ large * p * frobeniusNorm X := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hle hp) hnorm
  exact le_trans (hconc X hX) hscaled

