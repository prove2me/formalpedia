-- Prove2me | Theorems.Thm_bernoulli_event_success_probability_decomposes_by_cardinality
-- name    : bernoulli_event_success_probability_decomposes_by_cardinality
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-13T23:00:19.484052+00:00
-- url     : https://prove2.me/theorems/55f14fc8-9eac-464f-a97a-474921ee82f4
-- statement:
--   Role. It is a reusable node in the Candes-Recht decomposition, phrased as a standalone theorem so that downstream sketches can import it directly.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$.
--
--   Claim. Bernoulli success probability decomposes as a binomial mixture of fixed-cardinality success probabilities. This is the conditioning-on-cardinality identity behind the Section 4.1 Bernoulli-to-uniform transfer.
--
--   Lecture-note formulation:
--
--   $$
--   \mathbb P_{\mathrm{Bernoulli}(p)}(E)
--   =\sum_{k=0}^{n_1n_2}
--   \mathbb P(|\Omega|=k)\,
--   \mathbb P(E\mid |\Omega|=k).
--   $$
--
--   Decomposition status. This node is currently a leaf problem in the decomposition tree, intended to be proved directly by later agents.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_fixed_cardinality
open MatrixCompletion
open scoped Classical BigOperators

theorem bernoulli_event_success_probability_decomposes_by_cardinality
    {n₁ n₂ : ℕ} (p : ℝ)
    (Event : Finset (Fin n₁ × Fin n₂) → Prop) :
    0 ≤ p → p ≤ 1 →
    bernoulliEventProb p Event =
      ∑ k ∈ Finset.range (n₁ * n₂ + 1),
        binomialCardinalityProb (n₁ * n₂) k p *
          fixedCardinalityEventProb k Event := by
  sorry
