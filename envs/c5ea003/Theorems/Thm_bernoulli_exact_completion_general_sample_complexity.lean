-- Prove2me | Theorems.Thm_bernoulli_exact_completion_general_sample_complexity
-- name    : bernoulli_exact_completion_general_sample_complexity
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-13T20:48:30.95443+00:00
-- url     : https://prove2.me/theorems/7d73150f-2eee-46dd-a560-3ca72fa2ae33
-- statement:
--   Role. It is the Bernoulli-model version of the main theorem, before the final transfer to fixed-cardinality sampling.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$.
--
--   Claim. Candes-Recht Theorem 1.3, general branch, in the independent Bernoulli sampling model with inclusion probability $p = m/(n_{1}\,n_{2})$. This is the hard probabilistic core proved after the paper passes from fixed-cardinality sampling to Bernoulli sampling in Section 4.1.
--
--   Lecture-note formulation:
--
--   $$
--   \begin{gathered}
--   p=\frac{m}{n_1 n_2},\qquad n=\max(n_1,n_2),\\
--   m \ge C\,\max\!\left\{\mu_1^2,\sqrt{\mu_0}\mu_1,\mu_0 n^{1/4}\right\}
--         n r\,\beta\log n
--   \quad\Longrightarrow\quad
--   \mathbb P_p(\text{exact recovery of }M)\ge 1-c\,n^{-\beta}.
--   \end{gathered}
--   $$
--
--   The constants in this node are universal existential constants; the theorem asserts that some positive constants with these roles exist.
--
--   Decomposition status. A corresponding proof sketch reduces this node to smaller mathematical subclaims. The checked reduction uses 4 subclaims: Bernoulli restricted sampling injective under general sample bound; Bernoulli strict dual certificate under general sample bound; Bernoulli exact completion from injectivity and dual certificate; sample ratio between zero and one.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_bernoulli
open MatrixCompletion

theorem bernoulli_exact_completion_general_sample_complexity :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          C * max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                  (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4))
            * (↑(max n₁ n₂)) * (r : ℝ) * (β * Real.log (↑(max n₁ n₂))) →
        bernoulliSuccessProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) M ≥
          1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry
