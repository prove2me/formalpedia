-- Prove2me | Theorems.Thm_prefactored_centered_sampling_fluctuation_quadratic_threshold_from_mean_entry_scale
-- name    : prefactored_centered_sampling_fluctuation_quadratic_threshold_from_mean_entry_scale
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-14T02:10:46.205931+00:00
-- url     : https://prove2.me/theorems/4f322233-50bb-462d-89d2-2323bf2bb3be
-- statement:
--   Role. It is a centered-sampling fluctuation estimate, one of the reusable concentration interfaces used repeatedly by the Neumann-term bounds.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$.
--
--   Claim. Generic deterministic scale absorption for the mean part of the $\omega_{1} \ne \omega_{2} = \omega_{3}$ quadratic contribution. If the contribution is $(1-p)$ times a centered sampling fluctuation of a coefficient matrix with the deterministic mean-entry scale, then the fixed-matrix sampling event and Lemma 4.6 sample lower bound imply the $\lambda^{-3/2}$ threshold.
--
--   Lecture-note formulation:
--
--   $$
--   \text{centered-sampling bound}\times\text{deterministic prefactor}
--   \quad\Longrightarrow\quad
--   \text{the linear/quadratic Neumann coefficient threshold}.
--   $$
--
--   The constants in this node are universal existential constants; the theorem asserts that some positive constants with these roles exist.
--
--   Decomposition status. A corresponding proof sketch reduces this node to smaller mathematical subclaims. The checked reduction uses 2 subclaims: prefactored centered sampling fluctuation quadratic prefactor bound from mean entry scale; quadratic mean entry scale prefactor absorbed by sample lower.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem
    prefactored_centered_sampling_fluctuation_quadratic_threshold_from_mean_entry_scale
    (Cfixed Centry : ℝ) :
    0 < Cfixed → 0 < Centry →
    ∃ Cthreshold : ℝ, 0 < Cthreshold ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (μ₀ : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ →
        (m : ℝ) ≥
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
            (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              (β * Real.log (↑(max n₁ n₂))) →
        ∀ (Omega : Finset (Fin n₁ × Fin n₂))
          (X Y : Matrix (Fin n₁) (Fin n₂) ℝ),
        Y =
          (1 - ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) •
            centeredSamplingFluctuation Omega
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X →
        entrySupNorm X ≤
          Centry * μ₀ ^ 2 *
            (((r : ℝ) / (↑(max n₁ n₂))) ^ 2) *
              (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) →
        CenteredSamplingSpectralBound Omega
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X
            (Cfixed * Real.sqrt
              ((β * (↑(max n₁ n₂)) *
                  Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              entrySupNorm X) →
        spectralNorm Y ≤
          Cthreshold * Real.rpow lam (-((3 : ℝ) / 2)) := by
  sorry
