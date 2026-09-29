-- Prove2me | Theorems.Thm_inner_scaled_scalar_bernstein_lambda_scale_absorption
-- name    : inner_scaled_scalar_bernstein_lambda_scale_absorption
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-14T05:28:22.071502+00:00
-- url     : https://prove2.me/theorems/139f4953-edf8-48c0-8238-abc3284ea31d
-- statement:
--   Role. It is a scalar Bernstein-type tail estimate or deterministic scale absorption used to control sampled scalar fluctuations.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$.
--
--   Claim. Scalar arithmetic for the second all-distinct middle-coefficient Bernstein step. If the base entry/Frobenius scales already carry an inner $C_{\mathrm{inner}}\,\lambda^{-1/2}$ factor, the raw Bernstein scale is absorbed into $C_{\mathrm{inner}}\,\lambda^{-1}$.
--
--   Lecture-note formulation:
--
--   $$
--   \text{sample lower bound and coherence estimates}
--   \quad\Longrightarrow\quad
--   \operatorname{BernsteinScale}\le C\,\lambda^{-1}.
--   $$
--
--   The constants in this node are universal existential constants; the theorem asserts that some positive constants with these roles exist.
--
--   Decomposition status. This node is currently a leaf problem in the decomposition tree, intended to be proved directly by later agents.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem inner_scaled_scalar_bernstein_lambda_scale_absorption
    (Cbern Centry Cfro : ℝ) :
    0 < Cbern → 0 < Centry → 0 < Cfro →
    ∃ Cpoint : ℝ, 0 < Cpoint ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (μ₀ Cinner : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 0 < Cinner →
        (m : ℝ) ≥
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
            (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              (β * Real.log (↑(max n₁ n₂))) →
        Cbern *
            (Real.sqrt
                ((β * Real.log (↑(max n₁ n₂))) /
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              (Cfro * (Cinner * Real.rpow lam (-((1 : ℝ) / 2))) *
                Real.sqrt (μ₀ * ((r : ℝ) / (↑(max n₁ n₂))))) +
              ((β * Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              (Centry * (Cinner * Real.rpow lam (-((1 : ℝ) / 2))) *
                μ₀ * ((r : ℝ) / (↑(max n₁ n₂))))) ≤
          (Cpoint * Cinner) * Real.rpow lam (-1) := by
  sorry
