-- Prove2me | Theorems.Thm_quadratic_mean_response_rate_scale_absorbed_by_lambda_sample_bound
-- name    : quadratic_mean_response_rate_scale_absorbed_by_lambda_sample_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-14T04:38:39.977162+00:00
-- url     : https://prove2.me/theorems/9e3d4f3b-5cb9-4d52-9e00-7a44f87f668a
-- statement:
--   Role. It is a reusable node in the Candes-Recht decomposition, phrased as a standalone theorem so that downstream sketches can import it directly.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$.
--
--   Claim. Scalar absorption of the quadratic mean response-rate scale. The Lemma 4.6-style sample lower bound, together with the A0/default sign-entry scale, converts the response-transfer estimate into the displayed $\lambda^{-3/2}$ bound.
--
--   Lecture-note formulation:
--
--   $$
--   m\ge C\lambda\mu_0^{4/3}n r^{4/3}\beta\log n
--   \quad\Longrightarrow\quad
--   \text{quadratic mean response rate}\le C'\lambda^{-3/2}.
--   $$
--
--   The constants in this node are universal existential constants; the theorem asserts that some positive constants with these roles exist.
--
--   Decomposition status. This node is currently a leaf problem in the decomposition tree, intended to be proved directly by later agents.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_mean_response_rate_scale_absorbed_by_lambda_sample_bound
    (Cscale : ℝ) :
    0 < Cscale →
    ∃ Cthreshold : ℝ, 0 < Cthreshold ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ → A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
            (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              (β * Real.log (↑(max n₁ n₂))) →
        ∀ Y : Matrix (Fin n₁) (Fin n₂) ℝ,
        spectralNorm Y ≤
          Cscale * μ₀ * ((r : ℝ) / (↑(max n₁ n₂))) *
            Real.sqrt
              ((β * (↑(max n₁ n₂)) *
                  Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
            entrySupNorm
              ((((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) •
                signMatrix S) →
        spectralNorm Y ≤
          Cthreshold * Real.rpow lam (-((3 : ℝ) / 2)) := by
  sorry
