-- Prove2me | Theorems.Thm_quadratic_neumann_all_distinct_from_decoupled_bound
-- name    : quadratic_neumann_all_distinct_from_decoupled_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-14T00:26:59.402981+00:00
-- url     : https://prove2.me/theorems/8e25e434-fcc6-487a-a596-001b18d27af0
-- statement:
--   Role. It belongs to the golfing/Neumann-series certificate branch, where the certificate is decomposed into linear and quadratic sampling terms.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$. For certificate nodes, $T$ is the tangent space at $M$, $P_T$ and $P_{T^\perp}$ are the tangent and normal projections, and $P_\Omega$ keeps only observed entries. The Neumann-series estimates control the dual certificate used to prove uniqueness of nuclear-norm recovery.
--
--   Claim. Triple-decoupling transfer for the all-distinct quadratic Neumann term: control of the decoupled three-sample model implies control of the original all-distinct contribution, with only a universal constant loss.
--
--   Lecture-note formulation:
--
--   $$
--   \mathbb P(\|\left(Q_{1,2,3\ \mathrm{distinct}}\right)_{\mathrm{decoupled}}\|\le a)\ge 1-\varepsilon
--   \quad\Longrightarrow\quad
--   \mathbb P(\|Q_{1,2,3\ \mathrm{distinct}}\|\le C a)\ge 1-C\varepsilon.
--   $$
--
--   Decomposition status. A corresponding proof sketch reduces this node to smaller mathematical subclaims. The checked reduction uses 2 subclaims: quadratic Neumann all distinct triple decoupling tail bound; quadratic Neumann all distinct original tail from diagonal decoupled tail.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_all_distinct_from_decoupled_bound
    : ∃ K L : ℝ, 0 < K ∧ 0 < L ∧
      ∀ {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ} (S : SVD M r)
        (p Cdec cdec β lam : ℝ),
        0 ≤ p → p ≤ 1 → 0 < Cdec → 0 < cdec →
        bernoulliTripleEventProb p
            (fun Omega1 Omega2 Omega3 =>
              spectralNorm
                (quadraticNeumannAllDistinctDecoupledContribution
                  Omega1 Omega2 Omega3 S p) ≤
                Cdec * Real.rpow lam (-((3 : ℝ) / 2))) ≥
            1 - cdec * Real.rpow (↑(max n₁ n₂)) (-β) →
        bernoulliEventProb p
            (fun Omega =>
              spectralNorm (quadraticNeumannAllDistinctContribution Omega S p) ≤
                (K * Cdec) * Real.rpow lam (-((3 : ℝ) / 2))) ≥
          1 - (L * cdec) * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry
