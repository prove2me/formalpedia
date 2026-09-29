-- Prove2me | Theorems.Thm_linear_neumann_off_diagonal_pair_probability_from_coefficient_and_outer_conditional_bound
-- name    : linear_neumann_off_diagonal_pair_probability_from_coefficient_and_outer_conditional_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-14T01:34:08.452826+00:00
-- url     : https://prove2.me/theorems/ed8ec935-eb49-444a-b6f9-87c1d0f1eee1
-- statement:
--   Role. It belongs to the golfing/Neumann-series certificate branch, where the certificate is decomposed into linear and quadratic sampling terms.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$. For certificate nodes, $T$ is the tangent space at $M$, $P_T$ and $P_{T^\perp}$ are the tangent and normal projections, and $P_\Omega$ keeps only observed entries. The Neumann-series estimates control the dual certificate used to prove uniqueness of nuclear-norm recovery.
--
--   Claim. Pair-product probability lift for the decoupled off-diagonal linear Neumann term: combine the coefficient event in Ω₂ with the conditional outer sampling estimate in Ω₁.
--
--   Lecture-note formulation:
--
--   $$
--   \mathbb P(E_{\mathrm{coeff}})\ge 1-\varepsilon_1,\qquad
--   \mathbb P(E_{\mathrm{outer}}\mid E_{\mathrm{coeff}})\ge 1-\varepsilon_2
--   \quad\Longrightarrow\quad
--   \mathbb P(\|L_{\mathrm{off}}\|\le C\,\lambda^{-1})\ge 1-\varepsilon_1-\varepsilon_2.
--   $$
--
--   The constants in this node are universal existential constants; the theorem asserts that some positive constants with these roles exist.
--
--   Decomposition status. A corresponding proof sketch reduces this node to smaller mathematical subclaims. The checked reduction uses 2 subclaims: Bernoulli pair event probability from marginal and conditional lower bounds; sample ratio between zero and one.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem linear_neumann_off_diagonal_pair_probability_from_coefficient_and_outer_conditional_bound
    (Ccond ccond : ℝ) :
    0 < Ccond → 0 < ccond →
    ∃ Couter couter : ℝ, 0 < Couter ∧ 0 < couter ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          lam * μ₁ * max (Real.sqrt μ₀) μ₁ *
            (↑(max n₁ n₂)) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂))) →
        ∀ Ccoef ccoef : ℝ, 0 < Ccoef → 0 < ccoef →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega2 =>
              LinearNeumannOffDiagonalCoefficientBound Omega2 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (Ccoef * μ₁ *
                  Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                    Real.sqrt
                      ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
                          (β * Real.log (↑(max n₁ n₂)))) / (m : ℝ)))) ≥
          1 - ccoef * Real.rpow (↑(max n₁ n₂)) (-β) →
        (∀ Omega2 : Finset (Fin n₁ × Fin n₂),
          LinearNeumannOffDiagonalCoefficientBound Omega2 S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (Ccoef * μ₁ *
                Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                  Real.sqrt
                    ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
                        (β * Real.log (↑(max n₁ n₂)))) / (m : ℝ))) →
          bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega1 =>
                spectralNorm
                  (linearNeumannOffDiagonalDecoupledContribution
                    Omega1 Omega2 S
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
                  (Ccond * Ccoef) * Real.rpow lam (-1)) ≥
            1 - ccond * Real.rpow (↑(max n₁ n₂)) (-β)) →
        bernoulliPairEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega1 Omega2 =>
              spectralNorm
                (linearNeumannOffDiagonalDecoupledContribution
                  Omega1 Omega2 S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
                (Couter * Ccoef) * Real.rpow lam (-1)) ≥
          1 - (couter + ccoef) *
            Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry
