-- Prove2me | Theorems.Thm_bernoulli_moment_bound_from_symmetrization_and_auxiliary_moment_bound
-- name    : bernoulli_moment_bound_from_symmetrization_and_auxiliary_moment_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-13T23:06:05.904889+00:00
-- url     : https://prove2.me/theorems/80688c3f-d1e2-445f-8f8f-d53d94cf99c2
-- statement:
--   Role. It is a reusable node in the Candes-Recht decomposition, phrased as a standalone theorem so that downstream sketches can import it directly.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$.
--
--   Claim. Abstract moment transitivity for the symmetrization step. If a Bernoulli moment is bounded by $Csym^q$ times an auxiliary moment, and the auxiliary moment is bounded by $(Crad\,scale)^q$, then the original moment is bounded at the same scale after enlarging the universal constant.
--
--   Lecture-note formulation:
--
--   $$
--   \mathbb E\|Z-\mathbb EZ\|^q
--   \le 2^q\,\mathbb E\|Z-Z'\|^q
--   \le C^q\,\text{(auxiliary Rademacher moment scale)}^q.
--   $$
--
--   The constants in this node are universal existential constants; the theorem asserts that some positive constants with these roles exist.
--
--   Decomposition status. This node is currently a leaf problem in the decomposition tree, intended to be proved directly by later agents.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_bernoulli
open MatrixCompletion

theorem bernoulli_moment_bound_from_symmetrization_and_auxiliary_moment_bound
    (Csym Crad : ℝ) :
    0 < Csym →
    0 < Crad →
    ∃ Cq : ℝ, 0 < Cq ∧
      ∀ {n₁ n₂ : ℕ} (p scale : ℝ) (q : ℕ)
        (F G : Finset (Fin n₁ × Fin n₂) → ℝ),
        1 ≤ q →
        bernoulliExpectation p F ≤
          Csym ^ q * bernoulliExpectation p G →
        bernoulliExpectation p G ≤ (Crad * scale) ^ q →
        bernoulliExpectation p F ≤ (Cq * scale) ^ q := by
  sorry
