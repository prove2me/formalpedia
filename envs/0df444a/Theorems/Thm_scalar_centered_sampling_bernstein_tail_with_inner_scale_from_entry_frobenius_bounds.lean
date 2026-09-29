-- Prove2me | Theorems.Thm_scalar_centered_sampling_bernstein_tail_with_inner_scale_from_entry_frobenius_bounds
-- name    : scalar_centered_sampling_bernstein_tail_with_inner_scale_from_entry_frobenius_bounds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-14T05:23:43.010064+00:00
-- url     : https://prove2.me/theorems/ed0ab8ea-1e67-4169-8c11-f0277c81ff5c
-- statement:
--   Role. It is a centered-sampling fluctuation estimate, one of the reusable concentration interfaces used repeatedly by the Neumann-term bounds.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$.
--
--   Claim. Generic conditional scalar Bernstein estimate for the all-distinct middle coefficient scale. If the base matrix entry and Frobenius bounds carry an already-proved inner coefficient factor $C_{\mathrm{inner}}\,\lambda^{-1/2}$, the next scalar centered-sampling Bernstein step gives the $C_{\mathrm{inner}}\,\lambda^{-1}$ tail.
--
--   Lecture-note formulation:
--
--   $$
--   \|a\|_\infty\le a_\infty,\qquad \|a\|_2\le a_2
--   \Longrightarrow
--   \mathbb P_p\!\left(\left|\sum(\delta_{ij}-p)a_{ij}\right|
--   \le C\,\text{inner Bernstein scale}\right)\ge 1-cn^{-\beta}.
--   $$
--
--   The constants in this node are universal existential constants; the theorem asserts that some positive constants with these roles exist.
--
--   Decomposition status. A corresponding proof sketch reduces this node to smaller mathematical subclaims. The checked reduction uses 4 subclaims: scalar centered sampling bernstein tail from entry Frobenius scales; inner scaled scalar bernstein lambda scale absorption; Bernoulli event probability mono; sample ratio between zero and one.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem scalar_centered_sampling_bernstein_tail_with_inner_scale_from_entry_frobenius_bounds
    (Centry Cfro : ℝ) :
    0 < Centry → 0 < Cfro →
    ∃ Cpoint cpoint : ℝ, 0 < Cpoint ∧ 0 < cpoint ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (μ₀ Cinner : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 0 < Cinner →
        (m : ℝ) ≥
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
            (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              (β * Real.log (↑(max n₁ n₂))) →
        ∀ (Coeff : Finset (Fin n₁ × Fin n₂) → ℝ)
          (B : Matrix (Fin n₁) (Fin n₂) ℝ),
        (∀ Omega : Finset (Fin n₁ × Fin n₂),
          Coeff Omega =
            matrixEntrySum
              (centeredSamplingFluctuation Omega
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) B)) →
        entrySupNorm B ≤
          Centry * (Cinner * Real.rpow lam (-((1 : ℝ) / 2))) *
            μ₀ * ((r : ℝ) / (↑(max n₁ n₂))) →
        frobeniusNorm B ≤
          Cfro * (Cinner * Real.rpow lam (-((1 : ℝ) / 2))) *
            Real.sqrt (μ₀ * ((r : ℝ) / (↑(max n₁ n₂)))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              |Coeff Omega| ≤
                (Cpoint * Cinner) * Real.rpow lam (-1)) ≥
          1 - cpoint * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry
