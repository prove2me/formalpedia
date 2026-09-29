-- Prove2me | Theorems.Thm_quadratic_neumann_all_distinct_inner_base_frobenius_norm_bound_min_dim
-- name    : quadratic_neumann_all_distinct_inner_base_frobenius_norm_bound_min_dim
-- status  : Proved
-- author  : @Minghui
-- created : 2026-06-26T21:56:56.98866+00:00
-- url     : https://prove2.me/theorems/8f47f7ba-0d5a-4431-b38b-89756bdb6ded
-- statement:
--   Source:
--   Candès--Recht, *Exact Matrix Completion via Convex Optimization*, PDF p. 28, Section 6.2, Lemma 6.6, equations (6.15)--(6.17), and PDF p. 30, Section 6.3, equation (6.20).
--
--   Mathematical statement:
--   Let $S$ be rank-$r$ SVD data for $M\in\mathbb R^{n_1\times n_2}$ satisfying $A0(S,\mu_0)$ and $A1(S,\mu_1)$. For coordinates $w_1,w_2$, let $B^{\mathrm{all}}_{w_1,w_2}$ be `quadraticAllDistinctInnerBaseMatrix`, the all-distinct inner base matrix in the equation (6.20) branch. Then there is a universal positive constant $C_{\rm fro}$ such that
--   $$
--   \|B^{\mathrm{all}}_{w_1,w_2}\|_F
--   \le C_{\rm fro}\,\mu_1
--   \sqrt{\frac r{n_1n_2}}\,
--   \sqrt{\frac{\mu_0 r}{\min(n_1,n_2)}}.
--   $$
--
--   Notation context:
--   Downstream, $n=\max(n_1,n_2)$, $p=m/(n_1n_2)$ is the Bernoulli rate, and $\Omega$ is the sample set. This deterministic base-bound theorem itself does not quantify over $p$, $\Omega$, or $Z(\Omega)$. The parameters $\mu_0$ and $\mu_1$ are the Candès--Recht incoherence parameters from $A0$ and $A1$.
--
--   Formalization note:
--   This is a formal bridge, not a theorem stated verbatim in the paper. It composes the source-backed linear off-diagonal Frobenius base bound `linear_neumann_off_diagonal_coefficient_base_frobenius_norm_bound_min_dim` with the source-backed formal bridge `quadratic_neumann_all_distinct_inner_base_norms_le_linear_offdiag_base`, which says the all-distinct equation (6.20) base matrix is the Lemma 6.6 linear off-diagonal base matrix with one extra coordinate zeroed. This is the corrected min-dimension replacement for the disproved old max-denominator node `quadratic_neumann_all_distinct_inner_base_frobenius_norm_bound`.
-- source:
--   Candès--Recht, Exact Matrix Completion via Convex Optimization, PDF p. 28, Section 6.2, Lemma 6.6, equations (6.15)--(6.17), and PDF p. 30, Section 6.3, equation (6.20).

import Definitions.Def_linear_neumann_offdiag_bernstein
open MatrixCompletion
open scoped Classical BigOperators

theorem quadratic_neumann_all_distinct_inner_base_frobenius_norm_bound_min_dim :
    ∃ Cfro : ℝ, 0 < Cfro ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        ∀ w1 w2 : Fin n₁ × Fin n₂,
          frobeniusNorm (quadraticAllDistinctInnerBaseMatrix S w1 w2) ≤
            Cfro * μ₁ *
              Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                Real.sqrt
                  (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) := by
  sorry
