-- Prove2me | solution 1 for least_squares_certificate_with_normal_bound_is_strict_dual_certificate
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-06-20T15:21:16.288616+00:00
-- url     : https://prove2.me/submissions/242fedf8-2bc8-4fbb-be85-8676de4801be

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion
open scoped Classical BigOperators

theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (Omega : Finset (Fin n₁ × Fin n₂))
    (Y : Matrix (Fin n₁) (Fin n₂) ℝ) :
    LeastSquaresDualCertificate Omega S Y →
    spectralNorm (normalProjection S Y) < 1 →
    StrictDualCertificate Omega S Y := by
  intro hlsq hnorm
  exact ⟨hlsq.1, hlsq.2.1, hnorm⟩
