-- Prove2me | Theorems.Thm_linear_neumann_diagonal_centered_general_sample_threshold_from_min_dim_base_bound
-- name    : linear_neumann_diagonal_centered_general_sample_threshold_from_min_dim_base_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-30T15:48:30.014648+00:00
-- url     : https://prove2.me/theorems/9eef1fe3-4d7a-4596-bc68-c0b071b6832d
-- statement:
--   Deterministic scalar absorption for the centered diagonal first Neumann term under the corrected rectangular base-entry scale.
--
--   Context. In Candès--Recht Section 6.2, equation (6.9), the centered diagonal contribution is a scalar prefactor times the fixed-matrix centered sampling fluctuation of the diagonal base matrix $H$. The corrected rectangular estimate for $H$ uses $\min(n_1,n_2)$ in the denominator.
--
--   Claim. Under the full Theorem 1.3 sample lower bound
--   $$m\ge C'\max\{\mu_1^2,\sqrt{\mu_0}\mu_1,\mu_0 n^{1/4}\}nr\beta\log n,$$
--   with $C'$ large enough, the fixed-matrix centered sampling bound plus the representation (6.9) and the corrected base-entry bound imply the pointwise spectral estimate $\|S_{0,\mathrm{centered}}\|\le 1/32$.
--
--   Source: Candès--Recht 2008, PDF p. 6, Theorem 1.3/equation (1.9), PDF p. 26, equation (6.9), PDF p. 27, the centered-diagonal display after Theorem 6.3, and the rectangular convention immediately before Section 6.1.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem linear_neumann_diagonal_centered_general_sample_threshold_from_min_dim_base_bound
    (Cfixed Cbase : ℝ) :
    0 < Cfixed → 0 < Cbase →
    ∃ Cthreshold : ℝ, 0 < Cthreshold ∧
      ∀ C' : ℝ, Cthreshold ≤ C' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          C' * max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                  (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4))
            * (↑(max n₁ n₂)) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂))) →
        ∀ Omega : Finset (Fin n₁ × Fin n₂),
        linearNeumannDiagonalCenteredContribution Omega S
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) =
          (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹ *
              (1 - 2 * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))) •
            centeredSamplingFluctuation Omega
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (linearNeumannDiagonalBaseMatrix S) →
        entrySupNorm (linearNeumannDiagonalBaseMatrix S) ≤
          Cbase * μ₁ *
            Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) →
        CenteredSamplingSpectralBound Omega
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (linearNeumannDiagonalBaseMatrix S)
            (Cfixed * Real.sqrt
              ((β * (↑(max n₁ n₂)) *
                  Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              entrySupNorm (linearNeumannDiagonalBaseMatrix S)) →
        spectralNorm
            (linearNeumannDiagonalCenteredContribution Omega S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
          (1 : ℝ) / 32 := by
  sorry
