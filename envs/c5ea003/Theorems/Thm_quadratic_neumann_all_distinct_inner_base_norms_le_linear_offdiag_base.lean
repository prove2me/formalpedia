-- Prove2me | Theorems.Thm_quadratic_neumann_all_distinct_inner_base_norms_le_linear_offdiag_base
-- name    : quadratic_neumann_all_distinct_inner_base_norms_le_linear_offdiag_base
-- status  : Proved
-- author  : @Minghui
-- created : 2026-06-26T21:45:24.857391+00:00
-- url     : https://prove2.me/theorems/b7c3376d-0bb6-4a86-8b92-954b6f7abdd3
-- statement:
--   Source:
--   Candès--Recht, *Exact Matrix Completion via Convex Optimization*, PDF p. 28, Section 6.2, Lemma 6.6, equations (6.15)--(6.17), and PDF p. 30, Section 6.3, equation (6.20).
--
--   Mathematical statement:
--   For rank-$r$ SVD data $S$ of $M\in\mathbb R^{n_1\times n_2}$ and coordinates $w_1,w_2\in [n_1]\times[n_2]$, let
--   $$
--   B^{\mathrm{all}}_{w_1,w_2}(i,j)
--   =\begin{cases}
--   0, & (i,j)=w_1\text{ or }(i,j)=w_2,\\
--   \operatorname{sgn}(S)_{ij}\,K_S((i,j),w_2), & \text{otherwise},
--   \end{cases}
--   $$
--   be the all-distinct inner base matrix from the equation (6.20) branch. Let
--   $$
--   B^{\mathrm{lin}}_{w_2}(i,j)
--   =\begin{cases}
--   0, & (i,j)=w_2,\\
--   \operatorname{sgn}(S)_{ij}\,K_S((i,j),w_2), & \text{otherwise},
--   \end{cases}
--   $$
--   be the linear off-diagonal Lemma 6.6 base matrix. Then the extra zeroing at $w_1$ cannot increase either deterministic norm:
--   $$
--   \|B^{\mathrm{all}}_{w_1,w_2}\|_\infty
--   \le \|B^{\mathrm{lin}}_{w_2}\|_\infty,
--   \qquad
--   \|B^{\mathrm{all}}_{w_1,w_2}\|_F
--   \le \|B^{\mathrm{lin}}_{w_2}\|_F.
--   $$
--
--   Notation context:
--   Here $n=\max(n_1,n_2)$ is downstream matrix-completion notation, although it is not needed by this deterministic bridge. The Bernoulli rate $p=m/(n_1n_2)$ and sample set $\Omega$ are downstream in Lemma 6.6 and equation (6.20), but do not appear in this norm comparison. The coherence parameters $\mu_0$ and $\mu_1$ are used by the source-backed parent base-bound theorems, not by this zeroing bridge. $Z(\Omega)$ does not appear.
--
--   Formalization note:
--   This is a formal bridge, not a theorem stated verbatim in the paper. It connects the all-distinct equation (6.20) base matrix to the source-backed linear off-diagonal Lemma 6.6 base matrix by pointwise zeroing. The intended source-backed parent/import theorems are `linear_neumann_off_diagonal_coefficient_base_entry_sup_norm_bound_min_dim` and `linear_neumann_off_diagonal_coefficient_base_frobenius_norm_bound_min_dim`, whose source is Candès--Recht PDF p. 28, Section 6.2, Lemma 6.6, equations (6.15)--(6.17). This bridge is useful before deriving corrected all-distinct min-dimension base bounds, and it deliberately avoids the disproved old max-denominator all-distinct base-bound nodes.
-- source:
--   Candès--Recht, Exact Matrix Completion via Convex Optimization, PDF p. 28, Section 6.2, Lemma 6.6, equations (6.15)--(6.17), and PDF p. 30, Section 6.3, equation (6.20).

import Definitions.Def_linear_neumann_offdiag_bernstein
open MatrixCompletion
open scoped Classical BigOperators

theorem quadratic_neumann_all_distinct_inner_base_norms_le_linear_offdiag_base
    {n₁ n₂ r : Nat} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (w1 w2 : Fin n₁ × Fin n₂) :
    entrySupNorm (quadraticAllDistinctInnerBaseMatrix S w1 w2) ≤
        entrySupNorm (linearNeumannOffDiagonalCoefficientBaseMatrix S w2) ∧
      frobeniusNorm (quadraticAllDistinctInnerBaseMatrix S w1 w2) ≤
        frobeniusNorm (linearNeumannOffDiagonalCoefficientBaseMatrix S w2) := by
  sorry
