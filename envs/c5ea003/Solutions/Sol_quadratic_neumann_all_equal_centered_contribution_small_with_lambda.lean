-- Prove2me | solution 1 for quadratic_neumann_all_equal_centered_contribution_small_with_lambda
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-07-02T14:16:03.037949+00:00
-- url     : https://prove2.me/submissions/5bd3f9ca-3ffb-4adf-91bc-08a943dee5f7

import Theorems.Thm_fixed_matrix_centered_sampling_spectral_bound
import Theorems.Thm_quadratic_neumann_sample_lower_implies_fixed_matrix_sample_lower
import Theorems.Thm_quadratic_neumann_all_equal_centered_as_fixed_matrix_fluctuation
import Theorems.Thm_quadratic_neumann_all_equal_base_entry_sup_norm_bound_min_dim
import Theorems.Thm_quadratic_neumann_all_equal_centered_fixed_matrix_sampling_transfer_min_dim

open MatrixCompletion

/-- Source-backed repair for the centered all-equal term in Candes-Recht Lemma
4.6.  The decomposition follows Candes-Recht 2008, PDF p. 30, equation (6.21):
the all-equal cubic Bernoulli term splits into a centered fixed-matrix sampling
fluctuation and a deterministic mean term.  The centered part is then bounded by
Theorem 6.3 as used on PDF p. 30 immediately after equation (6.21).

Formalization note: this is a repair of the obsolete sketch that imported the
disproved max-dimension base-entry theorem
`quadratic_neumann_all_equal_base_entry_sup_norm_bound`.  The reduction now
imports the proved rectangular base estimate
`quadratic_neumann_all_equal_base_entry_sup_norm_bound_min_dim` and leaves the
remaining min-dimension scale absorption as the honest child
`quadratic_neumann_all_equal_centered_fixed_matrix_sampling_transfer_min_dim`. -/
theorem solution :
    ∃ Ccent ccent : ℝ, 0 < Ccent ∧ 0 < ccent ∧
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
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              spectralNorm
                (quadraticNeumannAllEqualCenteredContribution Omega S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
                Ccent * Real.rpow lam (-((3 : ℝ) / 2))) ≥
          1 - ccent * Real.rpow (↑(max n₁ n₂)) (-β) := by
  rcases fixed_matrix_centered_sampling_spectral_bound with
    ⟨Cfixed, hCfixed, hFixed⟩
  rcases quadratic_neumann_all_equal_base_entry_sup_norm_bound_min_dim with
    ⟨Cbase, hCbase, hBaseBound⟩
  rcases quadratic_neumann_all_equal_centered_fixed_matrix_sampling_transfer_min_dim
      Cfixed Cbase hCfixed hCbase with
    ⟨Ccent, ccent, hCcent, hccent, hTransfer⟩
  refine ⟨Ccent, ccent, hCcent, hccent, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
  have hFixedSample :
      (m : ℝ) ≥
        β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂)) :=
    quadratic_neumann_sample_lower_implies_fixed_matrix_sample_lower
      β lam n₁ n₂ r m μ₀ hβ hlam hn₁ hn₂ hr hμ₀ hmLower
  have hFixedProb :=
    hFixed β hβ n₁ n₂ m (quadraticNeumannAllEqualBaseMatrix S)
      hn₁ hn₂ hm hFixedSample
  have hRep :
      ∀ Omega : Finset (Fin n₁ × Fin n₂),
        quadraticNeumannAllEqualCenteredContribution Omega S
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) =
          ((((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) ^ 2 *
              (1 - 3 * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) +
                3 * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) ^ 2)) •
            centeredSamplingFluctuation Omega
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (quadraticNeumannAllEqualBaseMatrix S) := by
    intro Omega
    exact quadratic_neumann_all_equal_centered_as_fixed_matrix_fluctuation
      Omega S ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
  have hBase :=
    hBaseBound n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0
  exact hTransfer β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower hRep hBase hFixedProb
