-- Prove2me | Theorems.Thm_candes_recht_matrix_completion
-- name    : candes_recht_matrix_completion
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-13T20:42:07.19748+00:00
-- url     : https://prove2.me/theorems/e0ebc606-103e-4a0d-b4b8-58f4b7c1f1f8
-- title:
--   Candes-Recht Exact Matrix Completion
-- statement:
--   Role. It is the root theorem of the mission: the fixed-cardinality exact matrix completion guarantee corresponding to the general coherence branch of Theorem 1.3.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$.
--
--   Claim. Candes-Recht 2008, Theorem 1.3, general coherence-based sample complexity branch. There are universal constants $C, c > 0$ such that any rank-$r$ matrix obeying A0/A1 is recovered by nuclear-norm minimization from a uniformly random set of $m$ observed entries with probability at least $1 - c n^{-\beta}$, provided $m$ satisfies the displayed general sample lower bound.
--
--   Lecture-note formulation:
--
--   $$
--   \begin{gathered}
--   n=\max(n_1,n_2),\qquad
--   m \ge C\,\max\!\left\{\mu_1^2,\sqrt{\mu_0}\mu_1,\mu_0 n^{1/4}\right\}
--         n r\,\beta\log n\\
--   \Longrightarrow\quad
--   \mathbb P_{\Omega:\ |\Omega|=m}
--   \left(
--   \begin{array}{c}
--   \text{the nuclear-norm minimization problem}\\
--   \min\|X\|_*\ \text{ subject to }X_{ij}=M_{ij}\text{ for }(i,j)\in\Omega\\
--   \text{has the unique solution }X=M
--   \end{array}
--   \right)
--   \ge 1-c\,n^{-\beta}.
--   \end{gathered}
--   $$
--
--   The constants in this node are universal existential constants; the theorem asserts that some positive constants with these roles exist.
--
--   Decomposition status. A corresponding proof sketch reduces this node to smaller mathematical subclaims. The checked reduction uses 2 subclaims: Bernoulli exact completion general sample complexity; fixed cardinality completion probability from Bernoulli model.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_svd
open MatrixCompletion

theorem candes_recht_matrix_completion :
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
        successProb m M ≥ 1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry
