-- Prove2me | Theorems.Thm_bernoulli_nonnegative_statistic_moment_from_scaled_large_deviation_bound
-- name    : bernoulli_nonnegative_statistic_moment_from_scaled_large_deviation_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-13T23:07:07.920784+00:00
-- url     : https://prove2.me/theorems/98d88309-b064-4f70-9d88-f616e2e4a24a
-- statement:
--   Role. It is a reusable node in the Candes-Recht decomposition, phrased as a standalone theorem so that downstream sketches can import it directly.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$.
--
--   Claim. Generic tail-integration/summation step for a nonnegative Bernoulli statistic. If $F$ has the scaled large-deviation tail $P{F > \lambda p n} \le n exp(-\lambda p n/Cdev)$ for all $\lambda \ge 2$, then its $q$th moment is bounded by a universal multiple of $(p n)^q$ in the moment window used in Appendix 9.2.
--
--   Lecture-note formulation:
--
--   $$
--   \mathbb P(Z>\lambda A)\le B e^{-c\lambda A}
--   \quad(\lambda\ge2)
--   \Longrightarrow\quad
--   \mathbb E[Z^q]\le (C A)^q.
--   $$
--
--   The constants in this node are universal existential constants; the theorem asserts that some positive constants with these roles exist.
--
--   Decomposition status. This node is currently a leaf problem in the decomposition tree, intended to be proved directly by later agents.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_bernoulli
open MatrixCompletion

theorem bernoulli_nonnegative_statistic_moment_from_scaled_large_deviation_bound
    (Cdev : ℝ) :
    0 < Cdev →
    ∃ Cmoment : ℝ, 0 < Cmoment ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m q : ℕ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
        1 ≤ q →
        (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) →
        (q : ℝ) ≤
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) * (↑(max n₁ n₂)) →
        ∀ F : Finset (Fin n₁ × Fin n₂) → ℝ,
        (∀ Omega : Finset (Fin n₁ × Fin n₂), 0 ≤ F Omega) →
        (∀ lambda : ℝ, 2 ≤ lambda →
          bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega : Finset (Fin n₁ × Fin n₂) =>
                lambda *
                    (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                      (↑(max n₁ n₂))) <
                  F Omega) ≤
            (↑(max n₁ n₂)) *
              Real.exp
                (-(lambda *
                    (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                      (↑(max n₁ n₂)))) / Cdev)) →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega : Finset (Fin n₁ × Fin n₂) => F Omega ^ q) ≤
          (Cmoment * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
            (↑(max n₁ n₂))) ^ q := by
  sorry
