-- Prove2me | Theorems.Thm_left_singular_projection_matrix_spectral_norm_le_one
-- name    : left_singular_projection_matrix_spectral_norm_le_one
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-22T01:02:32.677441+00:00
-- url     : https://prove2.me/theorems/9fb1b8c6-92c5-456b-a7ed-a77fe0f8107d
-- statement:
--   This theorem says that the coordinate matrix $P_U$ of the left singular-vector projection has spectral norm at most one.
--
--   With
--   $$
--   (P_U)_{ia}=\sum_k u_k(i)u_k(a),
--   $$
--   the claim is
--   $$
--   \|P_U\|\le 1.
--   $$
--   This is the standard contraction property of orthogonal projections on Euclidean space.
--
--   Source: Candes-Recht 2008, PDF p. 15, Section 3, equation (3.5).
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem left_singular_projection_matrix_spectral_norm_le_one
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) :
    spectralNorm
        (fun i a : Fin n₁ => ∑ k : Fin r, S.u k i * S.u k a) ≤
      1 := by
  sorry
