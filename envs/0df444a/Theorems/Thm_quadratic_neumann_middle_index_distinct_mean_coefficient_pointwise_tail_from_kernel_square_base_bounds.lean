-- Prove2me | Theorems.Thm_quadratic_neumann_middle_index_distinct_mean_coefficient_pointwise_tail_from_kernel_square_base_bounds
-- name    : quadratic_neumann_middle_index_distinct_mean_coefficient_pointwise_tail_from_kernel_square_base_bounds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-14T02:18:31.887038+00:00
-- url     : https://prove2.me/theorems/883bdabd-ee35-4737-93fc-b182b833b00c
-- statement:
--   Role. It belongs to the golfing/Neumann-series certificate branch, where the certificate is decomposed into linear and quadratic sampling terms.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$. For certificate nodes, $T$ is the tangent space at $M$, $P_T$ and $P_{T^\perp}$ are the tangent and normal projections, and $P_\Omega$ keeps only observed entries. The Neumann-series estimates control the dual certificate used to prove uniqueness of nuclear-norm recovery.
--
--   Claim. Fixed-coordinate scalar Bernstein estimate for the mean coefficient $H_{\omega_{1}}$ in the $\omega_{1} = \omega_{3} \ne \omega_{2}$ quadratic term. For one outer index $w_{1}$, the centered-fluctuation representation and deterministic entry/Frobenius bounds for the kernel-square base matrix give the coefficient tail used before finite uniformization.
--
--   Lecture-note formulation:
--
--   $$
--   \begin{gathered}
--   \text{Here }B_w\text{ is the fixed base matrix and }G_w(\Omega)
--   \text{ is its scalar centered-sampling coefficient.}\\
--   \|B_{w}\|_\infty\le a_\infty,\qquad \|B_w\|_F\le a_F\\
--   \Longrightarrow\quad
--   \mathbb P_p\!\left(|G_w(\Omega)|\le C\,\lambda^{-1/2}\right)
--   \ge 1-c n^{-\beta}
--   \quad\text{for each fixed index }w .
--   \end{gathered}
--   $$
--
--   The constants in this node are universal existential constants; the theorem asserts that some positive constants with these roles exist.
--
--   Decomposition status. A corresponding proof sketch reduces this node to smaller mathematical subclaims. The checked reduction uses 1 subclaim: scalar centered sampling bernstein natural tail from quadratic base bounds.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem
    quadratic_neumann_middle_index_distinct_mean_coefficient_pointwise_tail_from_kernel_square_base_bounds
    (Centry Cfro : ℝ) :
    0 < Centry → 0 < Cfro →
    ∃ Cpoint cpoint : ℝ, 0 < Cpoint ∧ 0 < cpoint ∧
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
        ∀ w1 : Fin n₁ × Fin n₂,
        (∀ Omega : Finset (Fin n₁ × Fin n₂),
          quadraticMiddleIndexDistinctMeanCoefficient Omega S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1 =
            matrixEntrySum
              (centeredSamplingFluctuation Omega
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (quadraticMiddleIndexDistinctKernelSquareBaseMatrix S w1))) →
        entrySupNorm
            (quadraticMiddleIndexDistinctKernelSquareBaseMatrix S w1) ≤
          Centry * μ₀ ^ 2 *
            (((r : ℝ) / (↑(max n₁ n₂))) ^ 2) →
        frobeniusNorm
            (quadraticMiddleIndexDistinctKernelSquareBaseMatrix S w1) ≤
          Cfro * Real.rpow μ₀ ((3 : ℝ) / 2) *
            Real.rpow ((r : ℝ) / (↑(max n₁ n₂))) ((3 : ℝ) / 2) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              |quadraticMiddleIndexDistinctMeanCoefficient Omega S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1| ≤
                Cpoint *
                  Real.sqrt (β * Real.log (↑(max n₁ n₂))) *
                    Real.rpow
                      ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ)) / (m : ℝ))
                      ((3 : ℝ) / 2)) ≥
          1 - cpoint * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry
