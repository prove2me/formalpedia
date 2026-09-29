-- Prove2me | Theorems.Thm_sign_plus_normal_projection_operator_norm_le_one
-- name    : sign_plus_normal_projection_operator_norm_le_one
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-06-21T21:38:18.183828+00:00
-- url     : https://prove2.me/theorems/ac5b9eb5-4479-49d9-91ca-ca4564694126
-- statement:
--   **Sign matrix plus a normal-space contraction is a contraction (Candès–Recht 2009, arXiv:0805.4471, Lemma 3.2 achiever, p.15).** Let $E=\operatorname{sign}(M)$ be the tangent sign matrix of a rank-$r$ SVD $S$ of $M$, so $E\in T$ has column space inside the left singular span $U$ and row space inside the right singular span $V$. For any matrix $Z$ with operator norm $\lVert Z\rVert\le 1$, the normal projection $W=P_{T^\perp}Z$ lies in $T^\perp$ (its column space is orthogonal to $U$ and its row space orthogonal to $V$) and satisfies $\lVert W\rVert\le\lVert Z\rVert\le 1$ ($P_{T^\perp}$ is an operator-norm contraction). Because $E$ and $W$ have orthogonal column spaces and orthogonal row spaces, $E+W$ acts blockwise and $\lVert E+W\rVert=\max(\lVert E\rVert,\lVert W\rVert)\le 1$. This is exactly the construction guaranteeing $E+W\in\partial\lVert M\rVert_*$ in the subgradient characterization (3.4).
-- source:
--   Candès–Recht 2009, arXiv:0805.4471, Lemma 3.2 (p.15)

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem sign_plus_normal_projection_operator_norm_le_one {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ} (S : SVD M r) (Z : Matrix (Fin n₁) (Fin n₂) ℝ) (hZ : spectralNorm Z ≤ 1) : spectralNorm (signMatrix S + normalProjection S Z) ≤ 1 := by sorry
