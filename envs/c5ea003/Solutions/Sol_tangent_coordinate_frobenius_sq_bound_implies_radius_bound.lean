-- Prove2me | solution 1 for tangent_coordinate_frobenius_sq_bound_implies_radius_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-06-20T15:20:28.418046+00:00
-- url     : https://prove2.me/submissions/af9e47dd-261d-4325-9a45-64d24ebc81fd

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion
open scoped Classical BigOperators

theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (radiusSq : ℝ) :
    0 ≤ radiusSq →
    TangentCoordinateFrobeniusBound S radiusSq →
    ∀ i : Fin n₁, ∀ j : Fin n₂,
      frobeniusNorm (tangentProjection S (coordinateMatrix i j)) ≤
        Real.sqrt radiusSq := by
  intro _ hbound i j
  have ht : 0 ≤ frobeniusNorm (tangentProjection S (coordinateMatrix i j)) := by
    unfold frobeniusNorm; exact Real.sqrt_nonneg _
  have hb : frobeniusNorm (tangentProjection S (coordinateMatrix i j)) ^ 2 ≤ radiusSq :=
    hbound i j
  calc frobeniusNorm (tangentProjection S (coordinateMatrix i j))
      = Real.sqrt (frobeniusNorm (tangentProjection S (coordinateMatrix i j)) ^ 2) :=
        (Real.sqrt_sq ht).symm
    _ ≤ Real.sqrt radiusSq := Real.sqrt_le_sqrt hb
