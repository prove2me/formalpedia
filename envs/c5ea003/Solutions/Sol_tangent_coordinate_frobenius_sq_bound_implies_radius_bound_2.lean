-- Prove2me | solution 2 for tangent_coordinate_frobenius_sq_bound_implies_radius_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T03:11:24.618428+00:00
-- url     : https://prove2.me/submissions/8ac9e50f-15ec-4f9d-992f-ff9bfb6805ab

import Definitions.Def_matrix_completion_tangent

open MatrixCompletion

theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (radiusSq : ℝ) :
    0 ≤ radiusSq →
    TangentCoordinateFrobeniusBound S radiusSq →
    ∀ i : Fin n₁, ∀ j : Fin n₂,
      frobeniusNorm (tangentProjection S (coordinateMatrix i j)) ≤
        Real.sqrt radiusSq := by
  intro hradius hbound i j
  have hnorm_nonneg :
      0 ≤ frobeniusNorm (tangentProjection S (coordinateMatrix i j)) := by
    exact Real.sqrt_nonneg _
  exact (sq_le_sq₀ hnorm_nonneg (Real.sqrt_nonneg radiusSq)).mp (by
    simpa [Real.sq_sqrt hradius] using hbound i j)
