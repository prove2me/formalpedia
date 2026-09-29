-- Prove2me | Theorems.Thm_second_order_prefactored_centered_sampling_quadratic_prefactor_bound_from_min_dim_base_entry_scale
-- name    : second_order_prefactored_centered_sampling_quadratic_prefactor_bound_from_min_dim_base_entry_scale
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-03T21:58:38.131737+00:00
-- url     : https://prove2.me/theorems/651a67e6-7cb4-4d86-b154-f8ec6b6900f3
-- statement:
--   Raw fixed-matrix event step for the all-equal quadratic centered term with
--   prefactor `(p^{-1})^2(1 - 3p + 3p^2)`, leaving the scalar prefactor
--   unabsorbed, using the corrected `min n_1 n_2` base-entry scale.
--
--   Source: Candes-Recht 2008, PDF p. 30, equation (6.21), and the paragraph
--   immediately after it applying Theorem 6.3 to the first all-equal term.
-- source:
--   Candès-Recht 2008, PDF p. 30, equation (6.21), and the paragraph immediately after it applying Theorem 6.3 to the first all-equal term.

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem second_order_prefactored_centered_sampling_quadratic_prefactor_bound_from_min_dim_base_entry_scale
    (Cfixed Cbase : ℝ) :
    0 < Cfixed → 0 < Cbase →
    ∃ Cpref : ℝ, 0 < Cpref ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (μ₀ : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ →
        ∀ (Omega : Finset (Fin n₁ × Fin n₂))
          (B Y : Matrix (Fin n₁) (Fin n₂) ℝ),
        Y =
          ((((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) ^ 2 *
              (1 - 3 * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) +
                3 * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) ^ 2)) •
            centeredSamplingFluctuation Omega
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) B →
        entrySupNorm B ≤
          Cbase * μ₀ ^ 3 * (((r : ℝ) / (↑(min n₁ n₂))) ^ 3) →
        CenteredSamplingSpectralBound Omega
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) B
            (Cfixed * Real.sqrt
              ((β * (↑(max n₁ n₂)) *
                  Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              entrySupNorm B) →
        spectralNorm Y ≤
          Cpref * Cbase *
            |(((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) ^ 2 *
              (1 - 3 * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) +
                3 * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) ^ 2)| *
            μ₀ ^ 3 * (((r : ℝ) / (↑(min n₁ n₂))) ^ 3) *
            Real.sqrt
              ((β * (↑(max n₁ n₂)) *
                  Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) := by
  sorry
