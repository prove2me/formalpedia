-- Prove2me | solution 1 for linear_neumann_diagonal_mean_contribution_small_with_lambda
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-23T16:42:05.351244+00:00
-- url     : https://prove2.me/submissions/687613d4-2324-483b-b824-46704f473801

import Theorems.Thm_tangent_diagonal_multiplier_sign_spectral_norm_bound_from_a1
import Theorems.Thm_sign_matrix_spectral_norm_le_one
import Theorems.Thm_linear_neumann_diagonal_mean_as_scaled_diagonal_multiplier
import Theorems.Thm_linear_neumann_diagonal_mean_a1_scale_from_sample_lower
import Theorems.Thm_linear_neumann_diagonal_mean_bound_from_a1_multiplier_scale_of_nonneg
import Theorems.Thm_sample_ratio_between_zero_and_one
import Mathlib.Tactic.Positivity

open MatrixCompletion

/-!
Source: Candes-Recht 2008, PDF p. 26 equation (6.9) decomposes the diagonal
first Neumann term into a centered part and a deterministic mean part; PDF p. 27,
Lemma 6.4 equations (6.10)--(6.11), bounds the diagonal tangent-kernel
multiplier.  The repair here uses A1 (PDF p. 4) to control the actual
coordinate-energy scale of the sign matrix by `μ₁²`, avoiding the deprecated
loose A0/max-denominator absorption.
-/

/-- Bound the deterministic mean part of the diagonal first Neumann
contribution by Lemma 6.4 applied to the sign matrix with the A1-effective
scale, then absorb the scalar `p^{-1}(1-p)` using the Lemma 4.5 sample lower
bound. -/
theorem solution :
    ∃ Cmean : ℝ, 0 < Cmean ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          lam * μ₁ * max (Real.sqrt μ₀) μ₁ *
            (↑(max n₁ n₂)) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂))) →
        spectralNorm
            (linearNeumannDiagonalMeanContribution S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
          Cmean * Real.rpow lam (-1) := by
  rcases tangent_diagonal_multiplier_sign_spectral_norm_bound_from_a1 with
    ⟨Cdiag, hCdiag, hDiag⟩
  rcases linear_neumann_diagonal_mean_a1_scale_from_sample_lower Cdiag hCdiag with
    ⟨Cscale, hCscale, hScale⟩
  refine ⟨Cscale, hCscale, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ _hA0 hA1 hmLower
  let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
  rcases sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm with
    ⟨hpNonneg, hpLeOne⟩
  have hRep :
      linearNeumannDiagonalMeanContribution S p =
        (p⁻¹ * (1 - p)) • tangentDiagonalMultiplier S (signMatrix S) :=
    linear_neumann_diagonal_mean_as_scaled_diagonal_multiplier S p
  have hMultiplier :
      spectralNorm (tangentDiagonalMultiplier S (signMatrix S)) ≤
        Cdiag * (μ₁ ^ 2 * (r : ℝ) / (↑(min n₁ n₂))) *
          spectralNorm (signMatrix S) :=
    hDiag n₁ n₂ r M μ₁ S hn₁ hn₂ hr hμ₁ hA1
  have hSign : spectralNorm (signMatrix S) ≤ 1 :=
    sign_matrix_spectral_norm_le_one S
  have hScaleBound :
      Cdiag *
          ((p⁻¹ * (1 - p)) *
            (μ₁ ^ 2 * (r : ℝ) / (↑(min n₁ n₂)))) ≤
        Cscale * Real.rpow lam (-1) :=
    hScale β lam hβ hlam n₁ n₂ r m μ₀ μ₁
      hn₁ hn₂ hr hm hμ₀ hμ₁ hmLower
  have hdiagNonneg :
      0 ≤ Cdiag * (μ₁ ^ 2 * (r : ℝ) / (↑(min n₁ n₂))) := by
    have hnmin_pos_nat : 0 < min n₁ n₂ := lt_min hn₁ hn₂
    have hnmin_pos : 0 < (↑(min n₁ n₂) : ℝ) := by
      exact_mod_cast hnmin_pos_nat
    have hr_nonneg : 0 ≤ (r : ℝ) := by exact_mod_cast (Nat.zero_le r)
    have hμ₁sq_nonneg : 0 ≤ μ₁ ^ 2 := sq_nonneg μ₁
    positivity
  exact linear_neumann_diagonal_mean_bound_from_a1_multiplier_scale_of_nonneg
    S p Cdiag Cscale lam μ₁ hpNonneg hpLeOne hdiagNonneg hRep hMultiplier hSign hScaleBound
