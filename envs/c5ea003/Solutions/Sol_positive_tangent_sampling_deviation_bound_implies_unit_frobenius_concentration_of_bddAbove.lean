-- Prove2me | solution 1 for positive_tangent_sampling_deviation_bound_implies_unit_frobenius_concentration_of_bddAbove
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T06:42:39.20307+00:00
-- url     : https://prove2.me/submissions/a4b0fde0-5477-47af-ad07-f7ed9b89ea9a

import Definitions.Def_matrix_completion_tangent
import Mathlib.Tactic.Ring

open MatrixCompletion

theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p epsilon : ℝ) :
    BddAbove {v : ℝ |
      ∃ X : Matrix (Fin n₁) (Fin n₂) ℝ,
        tangentProjection S X = X ∧ frobeniusNorm X ≤ 1 ∧
          v = (p⁻¹) *
            frobeniusNorm
              (tangentProjection S (samplingProjection Omega X) - p • X)} →
    0 < p →
    TangentSamplingDeviationBound Omega S p epsilon →
    ∀ X : Matrix (Fin n₁) (Fin n₂) ℝ,
      tangentProjection S X = X →
      frobeniusNorm X ≤ 1 →
      frobeniusNorm
          (tangentProjection S (samplingProjection Omega X) - p • X) ≤
        epsilon * p := by
  intro hBdd hp hDeviation X hTangent hUnit
  let fluctuationNorm : ℝ :=
    frobeniusNorm
      (tangentProjection S (samplingProjection Omega X) - p • X)
  have hmem :
      (p⁻¹) * fluctuationNorm ∈ {v : ℝ |
        ∃ X : Matrix (Fin n₁) (Fin n₂) ℝ,
          tangentProjection S X = X ∧ frobeniusNorm X ≤ 1 ∧
            v = (p⁻¹) *
              frobeniusNorm
                (tangentProjection S (samplingProjection Omega X) - p • X)} := by
    refine ⟨X, hTangent, hUnit, ?_⟩
    rfl
  have hNormalized :
      (p⁻¹) * fluctuationNorm ≤ epsilon := by
    exact le_trans (le_csSup hBdd hmem) hDeviation
  have hmul := mul_le_mul_of_nonneg_left hNormalized (le_of_lt hp)
  have hp_ne : p ≠ 0 := ne_of_gt hp
  have hcancel : p * (p⁻¹ * fluctuationNorm) = fluctuationNorm := by
    rw [← mul_assoc, mul_inv_cancel₀ hp_ne, one_mul]
  have hcomm : p * epsilon = epsilon * p := by ring
  simpa [fluctuationNorm, hcancel, hcomm] using hmul
