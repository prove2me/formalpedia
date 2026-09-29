-- Prove2me | Theorems.Thm_quadratic_neumann_all_distinct_inner_coefficients_from_base_bounds
-- name    : quadratic_neumann_all_distinct_inner_coefficients_from_base_bounds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-14T02:12:31.20535+00:00
-- url     : https://prove2.me/theorems/2c3c29ce-8614-4612-9e96-2b586bdd3864
-- statement:
--   Role. It belongs to the golfing/Neumann-series certificate branch, where the certificate is decomposed into linear and quadratic sampling terms.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$. For certificate nodes, $T$ is the tangent space at $M$, $P_T$ and $P_{T^\perp}$ are the tangent and normal projections, and $P_\Omega$ keeps only observed entries. The Neumann-series estimates control the dual certificate used to prove uniqueness of nuclear-norm recovery.
--
--   Claim. Scalar Bernstein transfer for the inner $G_{\omega_{2}}$ coefficients in the all-distinct quadratic term. Given the centered-fluctuation representation and deterministic entry/Frobenius bounds for every fixed base matrix, the Lemma 4.6 sample lower bound gives the uniform $\lambda^{-1/2}$ coefficient event.
--
--   Lecture-note formulation:
--
--   $$
--   \text{entry and Frobenius bounds for each base matrix }B_w
--   \quad\Longrightarrow\quad
--   \text{the corresponding coefficient family for }Q_{1,2,3\ \mathrm{distinct}}\text{ is controlled}.
--   $$
--
--   The constants in this node are universal existential constants; the theorem asserts that some positive constants with these roles exist.
--
--   Decomposition status. A corresponding proof sketch reduces this node to smaller mathematical subclaims. The checked reduction uses 2 subclaims: quadratic Neumann all distinct inner coefficient pointwise tail from base bounds; quadratic Neumann all distinct inner coefficients uniform from pointwise tails.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_all_distinct_inner_coefficients_from_base_bounds
    (Centry Cfro : ℝ) :
    0 < Centry → 0 < Cfro →
    ∃ Cinner cinner : ℝ, 0 < Cinner ∧ 0 < cinner ∧
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
        (∀ (Omega3 : Finset (Fin n₁ × Fin n₂))
            (w1 w2 : Fin n₁ × Fin n₂),
          quadraticAllDistinctInnerCoefficient Omega3 S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1 w2 =
            matrixEntrySum
              (centeredSamplingFluctuation Omega3
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (quadraticAllDistinctInnerBaseMatrix S w1 w2))) →
        (∀ w1 w2 : Fin n₁ × Fin n₂,
          entrySupNorm (quadraticAllDistinctInnerBaseMatrix S w1 w2) ≤
            Centry * μ₀ ^ 2 *
              (((r : ℝ) / (↑(max n₁ n₂))) ^ 2)) →
        (∀ w1 w2 : Fin n₁ × Fin n₂,
          frobeniusNorm (quadraticAllDistinctInnerBaseMatrix S w1 w2) ≤
            Cfro * Real.rpow μ₀ ((3 : ℝ) / 2) *
              Real.rpow ((r : ℝ) / (↑(max n₁ n₂))) ((3 : ℝ) / 2)) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega3 =>
              QuadraticAllDistinctInnerCoefficientBound Omega3 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (Cinner * Real.rpow lam (-((1 : ℝ) / 2)))) ≥
          1 - cinner * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry
