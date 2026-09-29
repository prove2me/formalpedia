-- Prove2me | Theorems.Thm_matrix_inner_tangent_normal_decomposition_of_certificate
-- name    : matrix_inner_tangent_normal_decomposition_of_certificate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-14T00:57:47.00994+00:00
-- url     : https://prove2.me/theorems/2799128b-8d8d-4d98-b94d-aaee71ace9ad
-- statement:
--   This is the certificate-specialized Frobenius inner-product decomposition used in the deterministic dual-certificate argument.
--
--   Let $Y$ be a certificate whose tangent component is the sign matrix,
--   $$
--   P_TY=E=\operatorname{sign}(M).
--   $$
--   For every perturbation $H$, the Frobenius inner product splits as
--   $$
--   \langle Y,H\rangle_F
--   =
--   \langle E,P_TH\rangle_F+\langle P_{T^\perp}Y,P_{T^\perp}H\rangle_F.
--   $$
--   The theorem is just the general tangent/normal orthogonal decomposition with the hypothesis $P_TY=E$ substituted into the tangent term.
--
--   Source: Candes-Recht 2008, PDF p. 15, Section 3, equation (3.5), the decomposition $T\oplus T^\perp$, and the proof of Lemma 3.1.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem matrix_inner_tangent_normal_decomposition_of_certificate
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (Y H : Matrix (Fin n₁) (Fin n₂) ℝ) :
    tangentProjection S Y = signMatrix S →
    matrixInner Y H =
      matrixInner (signMatrix S) (tangentProjection S H) +
        matrixInner (normalProjection S Y) (normalProjection S H) := by
  sorry
