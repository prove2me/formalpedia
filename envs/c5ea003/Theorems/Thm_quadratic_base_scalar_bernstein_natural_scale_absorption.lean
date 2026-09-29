-- Prove2me | Theorems.Thm_quadratic_base_scalar_bernstein_natural_scale_absorption
-- name    : quadratic_base_scalar_bernstein_natural_scale_absorption
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-14T05:06:44.931349+00:00
-- url     : https://prove2.me/theorems/f4c4f764-a786-43ce-9751-41784e7dac41
-- statement:
--   Role. It is a scalar Bernstein-type tail estimate or deterministic scale absorption used to control sampled scalar fluctuations.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$.
--
--   Claim. Scalar arithmetic for the natural quadratic-kernel Bernstein scale. The raw entry/Frobenius Bernstein threshold is absorbed into the displayed natural scale under the Lemma 4.6 sample lower bound.
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

theorem quadratic_base_scalar_bernstein_natural_scale_absorption
    (Cbern Centry Cfro : ℝ) :
    0 < Cbern → 0 < Centry → 0 < Cfro →
    ∃ Cpoint : ℝ, 0 < Cpoint ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (μ₀ : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ →
        (m : ℝ) ≥
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
            (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              (β * Real.log (↑(max n₁ n₂))) →
        Cbern *
            (Real.sqrt
                ((β * Real.log (↑(max n₁ n₂))) /
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              (Cfro * Real.rpow μ₀ ((3 : ℝ) / 2) *
                Real.rpow ((r : ℝ) / (↑(max n₁ n₂))) ((3 : ℝ) / 2)) +
              ((β * Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              (Centry * μ₀ ^ 2 *
                (((r : ℝ) / (↑(max n₁ n₂))) ^ 2))) ≤
          Cpoint *
            Real.sqrt (β * Real.log (↑(max n₁ n₂))) *
              Real.rpow
                ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ)) / (m : ℝ))
                ((3 : ℝ) / 2) := by
  sorry
