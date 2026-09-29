-- Prove2me | Theorems.Thm_signed_kernel_square_bernstein_scale_compatibility_from_a0_sample_bound
-- name    : signed_kernel_square_bernstein_scale_compatibility_from_a0_sample_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-14T04:45:17.879074+00:00
-- url     : https://prove2.me/theorems/dbcc7928-57ef-4ce8-99f4-6dcca9557857
-- statement:
--   Role. It is a scalar Bernstein-type tail estimate or deterministic scale absorption used to control sampled scalar fluctuations.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$.
--
--   Claim. A0/default-sign scalar absorption for the signed kernel-square Bernstein step. Under the Lemma 4.6 sample lower bound, the sign entry times the natural quadratic scalar-Bernstein scale is absorbed into $\lambda^{-1}$.
--
--   Lecture-note formulation:
--
--   $$
--   \text{sample lower bound and coherence estimates}
--   \quad\Longrightarrow\quad
--   \operatorname{BernsteinScale}\le C\,\text{natural scale}.
--   $$
--
--   The constants in this node are universal existential constants; the theorem asserts that some positive constants with these roles exist.
--
--   Decomposition status. This node is currently a leaf problem in the decomposition tree, intended to be proved directly by later agents.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem signed_kernel_square_bernstein_scale_compatibility_from_a0_sample_bound :
    ∃ Ccompat : ℝ, 0 < Ccompat ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
            (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              (β * Real.log (↑(max n₁ n₂))) →
        ∀ w : Fin n₁ × Fin n₂,
        |signMatrix S w.1 w.2| *
            Real.sqrt (β * Real.log (↑(max n₁ n₂))) *
            Real.rpow
              ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ)) / (m : ℝ))
              ((3 : ℝ) / 2) ≤
          Ccompat * Real.rpow lam (-1) := by
  sorry
