-- Prove2me | Theorems.Thm_second_order_prefactored_centered_sampling_quadratic_threshold_from_base_entry_scale_min_dim
-- name    : second_order_prefactored_centered_sampling_quadratic_threshold_from_base_entry_scale_min_dim
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-07-03T13:35:10.849136+00:00
-- url     : https://prove2.me/theorems/17b086f9-b686-4f14-8b3f-a7227cba9b12
-- statement:
--   Min-dimension scalar threshold absorption for the all-equal quadratic centered prefactor $(p^{-1})^2(1-3p+3p^2)$ in the Candès-Recht Lemma 4.6 proof. Source: Candes-Recht 2008, PDF p. 30, equation (6.21), and the paragraph immediately following it applying Theorem 6.3 to the first all-equal term. This is the rectangular correction of the existing max-denominator threshold: the base matrix entry estimate is measured with $\min(n_1,n_2)$, matching the corrected A0 entry scale. The theorem is intentionally an open arithmetic leaf: it packages the scalar sample-size absorption from the Section 6.3 sample lower bound to the final $\lambda^{-3/2}$ spectral threshold.
-- source:
--   Candes-Recht 2008, PDF p. 30, equation (6.21) and following paragraph applying Theorem 6.3.

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem second_order_prefactored_centered_sampling_quadratic_threshold_from_base_entry_scale_min_dim
    (Cfixed Cbase : ℝ) :
    0 < Cfixed → 0 < Cbase →
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
          Cthreshold * Real.rpow lam (-((3 : ℝ) / 2)) := by
  sorry
