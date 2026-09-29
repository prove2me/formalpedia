-- Prove2me | Theorems.Thm_quadratic_neumann_first_index_distinct_centered_decoupled_threshold_from_centered_sampling_bound
-- name    : quadratic_neumann_first_index_distinct_centered_decoupled_threshold_from_centered_sampling_bound
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-06-14T02:15:21.957356+00:00
-- url     : https://prove2.me/theorems/4aa38f43-381f-4c6a-bdcf-ce68e6363895
-- statement:
--   Role. It belongs to the golfing/Neumann-series certificate branch, where the certificate is decomposed into linear and quadratic sampling terms.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$. For certificate nodes, $T$ is the tangent space at $M$, $P_T$ and $P_{T^\perp}$ are the tangent and normal projections, and $P_\Omega$ keeps only observed entries. The Neumann-series estimates control the dual certificate used to prove uniqueness of nuclear-norm recovery.
--
--   Claim. Deterministic threshold absorption for the decoupled centered $\omega_{1} \ne \omega_{2} = \omega_{3}$ contribution. For fixed Ω₂, the coefficient entry bound and the centered sampling spectral event in Ω₁ imply the desired $\lambda^{-3/2}$ spectral threshold after absorbing the scalar prefactor.
--
--   Lecture-note formulation:
--
--   $$
--   \|p^{-1}(P_\Omega-pI)B\|\le A(B)
--   \quad\Longrightarrow\quad
--   \|Q_{1\ne2=3}\|\le C\,\lambda^{-3/2}
--   \quad\text{after substituting the coefficient matrix }B.
--   $$
--
--   The constants in this node are universal existential constants; the theorem asserts that some positive constants with these roles exist.
--
--   Decomposition status. A corresponding proof sketch reduces this node to smaller mathematical subclaims. The checked reduction uses 1 subclaim: prefactored centered sampling fluctuation quadratic threshold from entry decay.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_first_index_distinct_centered_decoupled_threshold_from_centered_sampling_bound
    (Cfixed : ℝ) :
    0 < Cfixed →
    ∃ Cthreshold : ℝ, 0 < Cthreshold ∧
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
        ∀ Ccoef : ℝ, 0 < Ccoef →
        ∀ Omega1 Omega2 : Finset (Fin n₁ × Fin n₂),
        QuadraticFirstIndexDistinctCenteredCoefficientBound Omega2 S
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (Ccoef * Real.rpow lam (-1)) →
        quadraticNeumannFirstIndexDistinctCenteredDecoupledContribution
            Omega1 Omega2 S ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) =
          ((((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) *
              (1 - 2 * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))) •
            centeredSamplingFluctuation Omega1
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (quadraticFirstIndexDistinctCenteredCoefficientMatrix Omega2 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) →
        CenteredSamplingSpectralBound Omega1
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (quadraticFirstIndexDistinctCenteredCoefficientMatrix Omega2 S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))
            (Cfixed * Real.sqrt
              ((β * (↑(max n₁ n₂)) *
                  Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              entrySupNorm
                (quadraticFirstIndexDistinctCenteredCoefficientMatrix Omega2 S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))) →
        spectralNorm
            (quadraticNeumannFirstIndexDistinctCenteredDecoupledContribution
              Omega1 Omega2 S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
          (Cthreshold * Ccoef) * Real.rpow lam (-((3 : ℝ) / 2)) := by
  sorry
