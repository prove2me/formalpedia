-- Prove2me | Theorems.Thm_quadratic_neumann_middle_index_distinct_mean_prefactor_bound_from_coefficient_bound
-- name    : quadratic_neumann_middle_index_distinct_mean_prefactor_bound_from_coefficient_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-14T02:19:35.843071+00:00
-- url     : https://prove2.me/theorems/e856328e-d2bd-436b-ab8b-5b0fc27494c5
-- statement:
--   Role. It belongs to the golfing/Neumann-series certificate branch, where the certificate is decomposed into linear and quadratic sampling terms.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$. For certificate nodes, $T$ is the tangent space at $M$, $P_T$ and $P_{T^\perp}$ are the tangent and normal projections, and $P_\Omega$ keeps only observed entries. The Neumann-series estimates control the dual certificate used to prove uniqueness of nuclear-norm recovery.
--
--   Claim. Raw Frobenius comparison for the mean part of the $\omega_{1} = \omega_{3} \ne \omega_{2}$ quadratic term: the coefficient-sum representation, the Frobenius norm of the sign matrix, and a uniform coefficient bound imply the unabsorbed scalar prefactor.
--
--   Lecture-note formulation:
--
--   $$
--   \|Q_{1=3\ne2}\|
--   \le C\cdot \text{(coefficient bound)}
--      \cdot \text{(Frobenius/sign-matrix prefactor)}.
--   $$
--
--   The constants in this node are universal existential constants; the theorem asserts that some positive constants with these roles exist.
--
--   Decomposition status. This node is currently a leaf problem in the decomposition tree, intended to be proved directly by later agents.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_middle_index_distinct_mean_prefactor_bound_from_coefficient_bound :
    ∃ Cpref : ℝ, 0 < Cpref ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
        ∀ Omega : Finset (Fin n₁ × Fin n₂),
        quadraticNeumannMiddleIndexDistinctMeanContribution Omega S p =
          (p⁻¹ * (1 - p)) •
            ∑ w1 : Fin n₁ × Fin n₂,
              (signMatrix S w1.1 w1.2 *
                quadraticMiddleIndexDistinctMeanCoefficient Omega S p w1) •
                coordinateMatrix w1.1 w1.2 →
        frobeniusNorm (signMatrix S) ≤ Real.sqrt (r : ℝ) →
        ∀ Ccoef : ℝ, 0 < Ccoef →
        let coeffScale : ℝ :=
          Ccoef * Real.sqrt (β * Real.log (↑(max n₁ n₂))) *
            Real.rpow
              ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ)) / (m : ℝ))
              ((3 : ℝ) / 2)
        QuadraticMiddleIndexDistinctMeanCoefficientBound Omega S p coeffScale →
        spectralNorm
            (quadraticNeumannMiddleIndexDistinctMeanContribution Omega S p) ≤
          (Cpref * Ccoef) *
            (p⁻¹ * (1 - p)) *
            Real.sqrt (r : ℝ) *
            Real.sqrt (β * Real.log (↑(max n₁ n₂))) *
            Real.rpow
              ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ)) / (m : ℝ))
              ((3 : ℝ) / 2) := by
  sorry
