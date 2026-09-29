-- Prove2me | Theorems.Thm_quadratic_neumann_all_distinct_middle_pair_probability_from_inner_and_conditional_bound
-- name    : quadratic_neumann_all_distinct_middle_pair_probability_from_inner_and_conditional_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-14T04:40:03.714512+00:00
-- url     : https://prove2.me/theorems/21bbdb29-4677-4a8d-a496-f04673e090ba
-- statement:
--   Role. It belongs to the golfing/Neumann-series certificate branch, where the certificate is decomposed into linear and quadratic sampling terms.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$. For certificate nodes, $T$ is the tangent space at $M$, $P_T$ and $P_{T^\perp}$ are the tangent and normal projections, and $P_\Omega$ keeps only observed entries. The Neumann-series estimates control the dual certificate used to prove uniqueness of nuclear-norm recovery.
--
--   Claim. Product-probability lift for the all-distinct middle coefficient step: combine the high-probability inner Ω₃ event with the conditional high-probability Ω₂ Bernstein bound on that event.
--
--   Lecture-note formulation:
--
--   $$
--   \mathbb P(E_{\mathrm{coeff}})\ge 1-\varepsilon_1,\qquad
--   \mathbb P(E_{\mathrm{outer}}\mid E_{\mathrm{coeff}})\ge 1-\varepsilon_2
--   \quad\Longrightarrow\quad
--   \mathbb P(\|Q_{1,2,3\ \mathrm{distinct}}\|\le C\,\lambda^{-3/2})\ge 1-\varepsilon_1-\varepsilon_2.
--   $$
--
--   The constants in this node are universal existential constants; the theorem asserts that some positive constants with these roles exist.
--
--   Decomposition status. A corresponding proof sketch reduces this node to smaller mathematical subclaims. The checked reduction uses 2 subclaims: Bernoulli pair event probability from marginal and conditional lower bounds; sample ratio between zero and one.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_all_distinct_middle_pair_probability_from_inner_and_conditional_bound
    (Ccond ccond : ℝ) :
    0 < Ccond → 0 < ccond →
    ∃ Cstep cstep : ℝ, 0 < Cstep ∧ 0 < cstep ∧
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
        ∀ Cinner cinner : ℝ, 0 < Cinner → 0 < cinner →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega3 =>
              QuadraticAllDistinctInnerCoefficientBound Omega3 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (Cinner * Real.rpow lam (-((1 : ℝ) / 2)))) ≥
          1 - cinner * Real.rpow (↑(max n₁ n₂)) (-β) →
        (∀ Omega3 : Finset (Fin n₁ × Fin n₂),
          QuadraticAllDistinctInnerCoefficientBound Omega3 S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (Cinner * Real.rpow lam (-((1 : ℝ) / 2))) →
          bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega2 =>
                QuadraticAllDistinctMiddleCoefficientBound Omega2 Omega3 S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                  ((Ccond * Cinner) * Real.rpow lam (-1))) ≥
            1 - ccond * Real.rpow (↑(max n₁ n₂)) (-β)) →
        bernoulliPairEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega2 Omega3 =>
              QuadraticAllDistinctMiddleCoefficientBound Omega2 Omega3 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                ((Cstep * Cinner) * Real.rpow lam (-1))) ≥
          1 - (cstep + cinner) * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry
