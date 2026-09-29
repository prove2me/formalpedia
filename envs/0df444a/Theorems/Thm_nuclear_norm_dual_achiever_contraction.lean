-- Prove2me | Theorems.Thm_nuclear_norm_dual_achiever_contraction
-- name    : nuclear_norm_dual_achiever_contraction
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-06-21T21:38:00.545776+00:00
-- url     : https://prove2.me/theorems/61d86c4a-a436-41e3-9c15-ea23cf3e48da
-- statement:
--   **Nuclear-norm dual achiever (Candès–Recht 2009, arXiv:0805.4471, Lemma 3.2, p.15).** For every real matrix $N$ there is a contraction $Z$ in the operator (spectral) norm, $\lVert Z\rVert\le 1$, that realizes the nuclear norm of $N$ as a Frobenius inner product: $\langle Z, N\rangle = \lVert N\rVert_*$. Concretely, if $N=\sum_\ell\tilde\sigma_\ell\tilde u_\ell\tilde v_\ell^\top$ is an SVD of $N$, then $Z=\operatorname{sign}(N)=\sum_\ell\tilde u_\ell\tilde v_\ell^\top$ is a partial isometry with $\lVert Z\rVert=1$ (or $0$ when $N=0$) and $\langle Z,N\rangle=\sum_\ell\tilde\sigma_\ell=\lVert N\rVert_*$. This is the dual-norm duality $\lVert N\rVert_*=\max_{\lVert Z\rVert\le 1}\langle Z,N\rangle$, achieved at the sign matrix; it is the achiever half of trace duality (the equality case complementing the von Neumann inequality $\langle Z,N\rangle\le\lVert Z\rVert\,\lVert N\rVert_*$).
-- source:
--   Candès–Recht 2009, arXiv:0805.4471, Lemma 3.2 (p.15)

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem nuclear_norm_dual_achiever_contraction {n₁ n₂ : ℕ} (N : Matrix (Fin n₁) (Fin n₂) ℝ) : ∃ Z : Matrix (Fin n₁) (Fin n₂) ℝ, spectralNorm Z ≤ 1 ∧ matrixInner Z N = nuclearNorm N := by sorry
