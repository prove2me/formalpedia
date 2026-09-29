-- Prove2me | Theorems.Thm_matrix_inner_tangent_normal_orthogonal_decomposition
-- name    : matrix_inner_tangent_normal_orthogonal_decomposition
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-21T23:40:03.985252+00:00
-- url     : https://prove2.me/theorems/3673952a-f0c3-45ae-a4a7-fcad5930a009
-- statement:
--   This is the Frobenius inner-product decomposition associated with the tangent space $T$ and its orthogonal complement $T^\perp$.
--
--   Let $P_T$ be the orthogonal projection onto the tangent space at the rank-$r$ matrix and let $P_{T^\perp}=I-P_T$. For any two matrices $Y$ and $H$,
--   $$
--   \langle Y,H\rangle_F
--   =
--   \langle P_TY,P_TH\rangle_F+\langle P_{T^\perp}Y,P_{T^\perp}H\rangle_F.
--   $$
--   This is the basic Pythagorean/orthogonal-projection identity for the decomposition
--   $$
--   \mathbb R^{n_1\times n_2}=T\oplus T^\perp.
--   $$
--
--   Source: Candes-Recht 2008, PDF p. 15, Section 3, equation (3.5) and the paragraph introducing the orthogonal decomposition $T\oplus T^\perp$.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem matrix_inner_tangent_normal_orthogonal_decomposition
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (Y H : Matrix (Fin n₁) (Fin n₂) ℝ) :
    matrixInner Y H =
      matrixInner (tangentProjection S Y) (tangentProjection S H) +
        matrixInner (normalProjection S Y) (normalProjection S H) := by
  sorry
