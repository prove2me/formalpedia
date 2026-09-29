-- Prove2me | Theorems.Thm_normal_space_dual_achiever_with_sign_contraction
-- name    : normal_space_dual_achiever_with_sign_contraction
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-06-21T20:09:30.565829+00:00
-- url     : https://prove2.me/theorems/9b004c55-f204-4972-a228-43a02aab9cad
-- statement:
--   **Normal-space dual achiever with sign-contraction (Candès–Recht 2009, Lemma 3.2 achiever + subgradient characterization (3.4), p.15).** Given a rank-$r$ SVD $S$ of $M$ and any perturbation $H$, there exists a matrix $W$ lying in the normal space $T^\perp$ (i.e. $P_{T^\perp}W=W$, `normalProjection S W = W`) such that:
--   1. $E+W$ is a contraction in operator norm, $\|\operatorname{sign}(M)+W\|\le 1$ (`spectralNorm (signMatrix S + W) ≤ 1`); and
--   2. $W$ achieves the nuclear norm of the normal component of $H$: $\langle W,\ P_{T^\perp}H\rangle=\|P_{T^\perp}H\|_*$.
--   This is the achiever half of Lemma 3.2 ("there is a $W$ with $\|W\|=1$ achieving equality $\langle W,N\rangle=\|N\|_*$") specialized so that the achiever lives in $T^\perp$ and, combined with the tangent sign matrix $E\in T$ (orthogonal supports), keeps $\|E+W\|\le 1$. By the subgradient characterization (3.4), $E+W\in\partial\|M\|_*$. Construction: take $Z$ with $\|Z\|\le1$ and $\langle Z,P_{T^\perp}H\rangle=\|P_{T^\perp}H\|_*$ (dual achiever), set $W=P_{T^\perp}Z$; then $W\in T^\perp$, $\|W\|\le\|Z\|\le 1$ (since $P_{T^\perp}$ contracts the operator norm), $\langle W,P_{T^\perp}H\rangle=\langle Z,P_{T^\perp}H\rangle$, and $\|E+W\|=\max(\|E\|,\|W\|)=1$ because $E\in T,W\in T^\perp$ have orthogonal column/row spaces.
-- source:
--   Candès–Recht 2009, arXiv:0805.4471, Lemma 3.2 (p.15)

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem normal_space_dual_achiever_with_sign_contraction {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ} (S : SVD M r) (H : Matrix (Fin n₁) (Fin n₂) ℝ) : ∃ W : Matrix (Fin n₁) (Fin n₂) ℝ, normalProjection S W = W ∧ spectralNorm (signMatrix S + W) ≤ 1 ∧ matrixInner W (normalProjection S H) = nuclearNorm (normalProjection S H) := by sorry
