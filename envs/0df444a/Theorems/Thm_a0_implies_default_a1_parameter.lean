-- Prove2me | Theorems.Thm_a0_implies_default_a1_parameter
-- name    : a0_implies_default_a1_parameter
-- status  : Proved
-- author  : @Minghui
-- created : 2026-06-30T14:48:44.085033+00:00
-- url     : https://prove2.me/theorems/c4c4cef1-c05a-4c66-b578-fca7f7d680be
-- statement:
--   Cauchy--Schwarz consequence of Candes--Recht incoherence A0: A0 implies A1 with the default parameter $\mu_0\sqrt r$.
--
--   Primary reference: Candes--Recht, *Exact Matrix Completion via Convex Optimization*, PDF p. 6, Section 1.2, Definition 1.2 and the paragraph before Theorem 1.3, with Theorem 1.3 equation (1.9).  The paper states that if $A0(S,\mu_0)$ holds, then $A1(S,\mu_1)$ holds with $\mu_1=\mu_0\sqrt r$ by Cauchy--Schwarz.
--
--   Mathematical statement and notation: let $S=(\sigma_k,u_k,v_k)_{k=1}^r$ be rank-$r$ SVD data for an $n_1\times n_2$ real matrix $M$.  Assumption $A0(S,\mu_0)$ means
--   $$
--   \frac{n_1}{r}\max_i\sum_{k=1}^r u_k(i)^2\le \mu_0,
--   \qquad
--   \frac{n_2}{r}\max_j\sum_{k=1}^r v_k(j)^2\le \mu_0.
--   $$
--   The sign matrix is
--   $$
--   E_{ij}=\sum_{k=1}^r u_k(i)v_k(j).
--   $$
--   The theorem proves that for $n_1,n_2,r>0$ and $\mu_0\ge0$,
--   $$
--   |E_{ij}|\le \mu_0\sqrt r\sqrt{\frac{r}{n_1n_2}}
--   $$
--   for all $i,j$, which is exactly $A1(S,\operatorname{defaultA1Parameter}(\mu_0,r))$ in the local definitions.
--
--   Variables and unused quantities: $n_1,n_2,r,M,S,\mu_0$ are active.  The sampling rate $p$, sample set $\Omega$, random variable $Z(\Omega)$, ambient $\mu_1$, Bernoulli/fixed-cardinality probability model, and `successProb` do not appear in this deterministic SVD-coherence bridge.
--
--   Formalization note: this is a source-derived theorem, not a theorem stated verbatim as a numbered lemma and not a purely formal Lean bridge.  It packages the cited Candes--Recht Cauchy--Schwarz observation into a reusable Lean node for downstream source-backed Lemma 6.6 routes, including the structural all-distinct coefficient branch.
-- source:
--   Candes--Recht, *Exact Matrix Completion via Convex Optimization*, PDF p. 6, Section 1.2, Definition 1.2 and paragraph before Theorem 1.3, with Theorem 1.3 equation (1.9).

import Definitions.Def_matrix_completion_svd
open MatrixCompletion

theorem a0_implies_default_a1_parameter :
    ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
      (μ₀ : ℝ) (S : SVD M r),
      0 < n₁ → 0 < n₂ → 0 < r →
      0 ≤ μ₀ → A0 S μ₀ → A1 S (defaultA1Parameter μ₀ r) := by
  sorry
