-- Prove2me | Theorems.Thm_centered_sampling_fluctuation_linear_neumann_prefactor_bound_from_entry_scale
-- name    : centered_sampling_fluctuation_linear_neumann_prefactor_bound_from_entry_scale
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-13T23:17:57.878208+00:00
-- url     : https://prove2.me/theorems/2655dc3f-4f03-4c0f-bc99-a1a00ea710db
-- statement:
--   Role. It belongs to the golfing/Neumann-series certificate branch, where the certificate is decomposed into linear and quadratic sampling terms.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$. For certificate nodes, $T$ is the tangent space at $M$, $P_T$ and $P_{T^\perp}$ are the tangent and normal projections, and $P_\Omega$ keeps only observed entries. The Neumann-series estimates control the dual certificate used to prove uniqueness of nuclear-norm recovery.
--
--   Claim. Raw deterministic step for a linear Neumann centered-sampling fluctuation: the fixed-matrix sampling event and the entry-scale hypothesis give the unabsorbed prefactor scale.
--
--   Lecture-note formulation:
--
--   $$
--   \|L\|
--   \le C\cdot \text{(coefficient bound)}
--      \cdot \text{(Frobenius/sign-matrix prefactor)}.
--   $$
--
--   The constants in this node are universal existential constants; the theorem asserts that some positive constants with these roles exist.
--
--   Decomposition status. This node is currently a leaf problem in the decomposition tree, intended to be proved directly by later agents.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem centered_sampling_fluctuation_linear_neumann_prefactor_bound_from_entry_scale
    (Cfixed : ℝ) :
    0 < Cfixed →
    ∃ Cpref : ℝ, 0 < Cpref ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (μ₀ μ₁ : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
        ∀ Centry : ℝ, 0 < Centry →
        let entryScale : ℝ :=
          Centry * μ₁ *
            Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              Real.sqrt
                ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
                    (β * Real.log (↑(max n₁ n₂)))) / (m : ℝ))
        ∀ (Omega : Finset (Fin n₁ × Fin n₂))
          (X Y : Matrix (Fin n₁) (Fin n₂) ℝ),
        Y = centeredSamplingFluctuation Omega p X →
        entrySupNorm X ≤ entryScale →
        CenteredSamplingSpectralBound Omega
            p X
            (Cfixed * Real.sqrt
              ((β * (↑(max n₁ n₂)) *
                  Real.log (↑(max n₁ n₂))) /
                p) *
              entrySupNorm X) →
        spectralNorm Y ≤
          Cpref * entryScale *
            Real.sqrt
              ((β * (↑(max n₁ n₂)) *
                  Real.log (↑(max n₁ n₂))) /
                p) := by
  sorry
