-- Prove2me | solution 2 for least_squares_certificate_with_normal_bound_is_strict_dual_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-20T20:14:21.13921+00:00
-- url     : https://prove2.me/submissions/df0d4562-7159-435f-8b35-638ec1241007

import Definitions.Def_matrix_completion_tangent

open MatrixCompletion

theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (Omega : Finset (Fin n₁ × Fin n₂))
    (Y : Matrix (Fin n₁) (Fin n₂) ℝ) :
    LeastSquaresDualCertificate Omega S Y →
    spectralNorm (normalProjection S Y) < 1 →
    StrictDualCertificate Omega S Y := by
  intro hcert hnormal
  rcases hcert with ⟨hsupport, htangent, _hmin⟩
  exact ⟨hsupport, htangent, hnormal⟩

