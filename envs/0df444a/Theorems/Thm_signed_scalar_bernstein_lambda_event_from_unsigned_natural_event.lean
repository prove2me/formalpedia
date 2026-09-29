-- Prove2me | Theorems.Thm_signed_scalar_bernstein_lambda_event_from_unsigned_natural_event
-- name    : signed_scalar_bernstein_lambda_event_from_unsigned_natural_event
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-14T05:24:04.540147+00:00
-- url     : https://prove2.me/theorems/4762d4d5-cc7c-4a6e-9f83-b186b6427e66
-- statement:
--   Role. It is a scalar Bernstein-type tail estimate or deterministic scale absorption used to control sampled scalar fluctuations.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$.
--
--   Claim. Pointwise deterministic transfer from the unsigned natural-scale scalar Bernstein event to the signed $\lambda^{-1}$ event. This isolates the coefficient identity and the Lemma 4.6 sign/sample compatibility from probability monotonicity.
--
--   Lecture-note formulation:
--
--   $$
--   \{|Z|\le a_{\mathrm{natural}}\}\subseteq \{|Z|\le a_{\lambda}\}
--   \quad\Longrightarrow\quad
--   \mathbb P(|Z|\le a_\lambda)\ge \mathbb P(|Z|\le a_{\mathrm{natural}}).
--   $$
--
--   The constants in this node are universal existential constants; the theorem asserts that some positive constants with these roles exist.
--
--   Decomposition status. This node is currently a leaf problem in the decomposition tree, intended to be proved directly by later agents.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem signed_scalar_bernstein_lambda_event_from_unsigned_natural_event
    (Cnatural Ccompat : ℝ) :
    0 < Cnatural → 0 < Ccompat →
    ∃ Cpoint : ℝ, 0 < Cpoint ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (μ₀ sign : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ →
        |sign| *
            Real.sqrt (β * Real.log (↑(max n₁ n₂))) *
            Real.rpow
              ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ)) / (m : ℝ))
              ((3 : ℝ) / 2) ≤
          Ccompat * Real.rpow lam (-1) →
        ∀ (Coeff : Finset (Fin n₁ × Fin n₂) → ℝ)
          (B : Matrix (Fin n₁) (Fin n₂) ℝ),
        (∀ Omega : Finset (Fin n₁ × Fin n₂),
          Coeff Omega =
            sign *
              matrixEntrySum
                (centeredSamplingFluctuation Omega
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) B)) →
        ∀ Omega : Finset (Fin n₁ × Fin n₂),
        |matrixEntrySum
            (centeredSamplingFluctuation Omega
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) B)| ≤
          Cnatural *
            Real.sqrt (β * Real.log (↑(max n₁ n₂))) *
              Real.rpow
                ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ)) / (m : ℝ))
                ((3 : ℝ) / 2) →
        |Coeff Omega| ≤ Cpoint * Real.rpow lam (-1) := by
  sorry
