-- Prove2me | Theorems.Thm_off_diagonal_tangent_response_eq_tangent_projection_sub_diagonal_multiplier
-- name    : off_diagonal_tangent_response_eq_tangent_projection_sub_diagonal_multiplier
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-22T00:27:43.008454+00:00
-- url     : https://prove2.me/theorems/eada1060-e901-425e-850f-5e33eed7ca72
-- statement:
--   This is the algebraic decomposition of the off-diagonal tangent response.
--
--   Let $R_{\mathrm{off}}$ be the operator whose $(a,b)$ entry sums
--   $$
--   \sum_{(a',b')\ne(a,b)} X_{a'b'}\,
--   \langle P_T(e_{a'}e_{b'}^*),e_ae_b^*\rangle.
--   $$
--   Let $D_T$ be the diagonal tangent-kernel multiplier
--   $$
--   (D_T X)_{ab}=X_{ab}\,\langle P_T(e_ae_b^*),e_ae_b^*\rangle.
--   $$
--   The theorem states
--   $$
--   R_{\mathrm{off}}(X)=P_T(X)-D_T(X).
--   $$
--   In Lean, these are `offDiagonalTangentResponse`, `tangentProjection`, and `tangentDiagonalMultiplier`.
--
--   Source: Candes-Recht 2008, PDF p. 26, Section 6.2, equations (6.13)--(6.14), together with the tangent-kernel formula (6.1) on PDF p. 23.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem off_diagonal_tangent_response_eq_tangent_projection_sub_diagonal_multiplier
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    offDiagonalTangentResponse S X =
      tangentProjection S X - tangentDiagonalMultiplier S X := by
  sorry
