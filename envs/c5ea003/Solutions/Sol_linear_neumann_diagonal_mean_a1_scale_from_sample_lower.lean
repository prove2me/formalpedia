-- Prove2me | solution 1 for linear_neumann_diagonal_mean_a1_scale_from_sample_lower
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-23T16:59:55.056578+00:00
-- url     : https://prove2.me/submissions/263cbcf4-fed9-46f9-9a5c-321d37f83c22

import Definitions.Def_matrix_completion_neumann
import Mathlib.Tactic

open MatrixCompletion

private lemma rectangular_cardinality_div_min_le_max
    {n₁ n₂ : ℕ} (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) :
    ((n₁ : ℝ) * (n₂ : ℝ)) / (((min n₁ n₂ : ℕ) : ℝ)) ≤
      (((max n₁ n₂ : ℕ) : ℝ)) := by
  by_cases hle : n₁ ≤ n₂
  · have hmin : min n₁ n₂ = n₁ := Nat.min_eq_left hle
    have hmax : max n₁ n₂ = n₂ := Nat.max_eq_right hle
    have hn₁_ne : (n₁ : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn₁)
    rw [hmin, hmax]
    field_simp [hn₁_ne]
    norm_num
  · have hle' : n₂ ≤ n₁ := le_of_not_ge hle
    have hmin : min n₁ n₂ = n₂ := Nat.min_eq_right hle'
    have hmax : max n₁ n₂ = n₁ := Nat.max_eq_left hle'
    have hn₂_ne : (n₂ : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn₂)
    rw [hmin, hmax]
    field_simp [hn₂_ne]
    norm_num

private lemma sample_ratio_inverse_one_minus_le_card_div_sample
    {n₁ n₂ m : ℕ} (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hm : m ≤ n₁ * n₂)
    (hm_pos : 0 < m) :
    ((((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) *
        (1 - ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))) ≤
      ((n₁ : ℝ) * (n₂ : ℝ)) / (m : ℝ) := by
  let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
  have hden_pos : 0 < (n₁ : ℝ) * (n₂ : ℝ) :=
    mul_pos (Nat.cast_pos.mpr hn₁) (Nat.cast_pos.mpr hn₂)
  have hm_pos_real : 0 < (m : ℝ) := Nat.cast_pos.mpr hm_pos
  have hp_nonneg : 0 ≤ p := by
    dsimp [p]
    positivity
  have hp_le_one : p ≤ 1 := by
    dsimp [p]
    rw [div_le_iff₀ hden_pos]
    have hm_real : (m : ℝ) ≤ (n₁ : ℝ) * (n₂ : ℝ) := by exact_mod_cast hm
    simpa using hm_real
  have hone_sub_le_one : 1 - p ≤ 1 := by linarith
  have hp_inv_nonneg : 0 ≤ p⁻¹ := by exact inv_nonneg.mpr hp_nonneg
  have hmain : p⁻¹ * (1 - p) ≤ p⁻¹ := by
    simpa using mul_le_mul_of_nonneg_left hone_sub_le_one hp_inv_nonneg
  have hp_inv_eq : p⁻¹ = ((n₁ : ℝ) * (n₂ : ℝ)) / (m : ℝ) := by
    dsimp [p]
    field_simp [hden_pos.ne', hm_pos_real.ne']
  simpa [p, hp_inv_eq] using hmain

theorem solution
    (Cdiag : ℝ) :
    0 < Cdiag →
    ∃ Cscale : ℝ, 0 < Cscale ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (μ₀ μ₁ : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        (m : ℝ) ≥
          lam * μ₁ * max (Real.sqrt μ₀) μ₁ *
            (↑(max n₁ n₂)) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂))) →
        Cdiag *
            ((((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹ *
                (1 - ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))) *
              (μ₁ ^ 2 * (r : ℝ) / (↑(min n₁ n₂)))) ≤
          Cscale * Real.rpow lam (-1) := by
  intro hCdiag
  refine ⟨Cdiag * (Real.log (2 : ℝ))⁻¹, ?_, ?_⟩
  · exact mul_pos hCdiag (inv_pos.mpr (Real.log_pos (by norm_num : (1 : ℝ) < 2)))
  · intro β lam hβ hlam n₁ n₂ r m μ₀ μ₁ hn₁ hn₂ hr hm hμ₀ hμ₁ hmLower
    let N : ℕ := max n₁ n₂
    let A : ℝ := max (Real.sqrt μ₀) μ₁
    let L : ℝ := β * Real.log (N : ℝ)
    let X : ℝ := μ₁ ^ 2 * (N : ℝ) * (r : ℝ)
    have hCdiag_nonneg : 0 ≤ Cdiag := le_of_lt hCdiag
    have hlog2_pos : 0 < Real.log (2 : ℝ) :=
      Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have hlam_pos : 0 < lam := lt_of_lt_of_le zero_lt_one hlam
    have hμ₁_nonneg : 0 ≤ μ₁ := le_trans zero_le_one hμ₁
    have hμ₁_sq_nonneg : 0 ≤ μ₁ ^ 2 := sq_nonneg μ₁
    have hr_real_pos : 0 < (r : ℝ) := Nat.cast_pos.mpr hr
    have hmin_pos_nat : 0 < min n₁ n₂ := by omega
    have hmin_pos : 0 < (((min n₁ n₂ : ℕ) : ℝ)) := Nat.cast_pos.mpr hmin_pos_nat
    have hN_pos_nat : 0 < N := by
      dsimp [N]
      exact lt_of_lt_of_le hn₁ (Nat.le_max_left n₁ n₂)
    have hN_pos : 0 < (N : ℝ) := Nat.cast_pos.mpr hN_pos_nat
    have hX_nonneg : 0 ≤ X := by
      dsimp [X]
      positivity
    have hRpow : Real.rpow lam (-1) = lam⁻¹ := Real.rpow_neg_one lam
    have hRhs_nonneg :
        0 ≤ (Cdiag * (Real.log (2 : ℝ))⁻¹) * Real.rpow lam (-1) := by
      rw [hRpow]
      positivity
    by_cases hN_one : N = 1
    · have hn₁_one : n₁ = 1 := by
        dsimp [N] at hN_one
        omega
      have hn₂_one : n₂ = 1 := by
        dsimp [N] at hN_one
        omega
      have hm_le_one : m ≤ 1 := by
        have hprod_one : n₁ * n₂ = 1 := by rw [hn₁_one, hn₂_one]
        simpa [hprod_one] using hm
      have hm_cases : m = 0 ∨ m = 1 := by omega
      rcases hm_cases with hm_zero | hm_one
      · simpa [hm_zero, hn₁_one, hn₂_one] using hRhs_nonneg
      · simpa [hm_one, hn₁_one, hn₂_one] using hRhs_nonneg
    · have hN_ge_two_nat : 2 ≤ N := by omega
      have hN_ge_two : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN_ge_two_nat
      have hlog_ge_log2 : Real.log (2 : ℝ) ≤ Real.log (N : ℝ) :=
        Real.log_le_log (by norm_num : (0 : ℝ) < 2) hN_ge_two
      have hlogN_nonneg : 0 ≤ Real.log (N : ℝ) :=
        le_trans (le_of_lt hlog2_pos) hlog_ge_log2
      have hβ_ge_one : (1 : ℝ) ≤ β := by linarith
      have hlogN_le_L : Real.log (N : ℝ) ≤ L := by
        have htmp :
            (1 : ℝ) * Real.log (N : ℝ) ≤ β * Real.log (N : ℝ) :=
          mul_le_mul_of_nonneg_right hβ_ge_one hlogN_nonneg
        simpa [L] using htmp
      have hL_ge_log2 : Real.log (2 : ℝ) ≤ L :=
        le_trans hlog_ge_log2 hlogN_le_L
      have hL_pos : 0 < L := lt_of_lt_of_le hlog2_pos hL_ge_log2
      have hA_ge_mu : μ₁ ≤ A := by
        dsimp [A]
        exact le_max_right _ _
      have hA_nonneg : 0 ≤ A := le_trans hμ₁_nonneg hA_ge_mu
      have hmuA_ge_musq : μ₁ ^ 2 ≤ μ₁ * A := by
        have hmul := mul_le_mul_of_nonneg_left hA_ge_mu hμ₁_nonneg
        simpa [sq] using hmul
      have htail_nonneg :
          0 ≤ (N : ℝ) * (r : ℝ) * L := by
        positivity
      have hsample_core :
          lam * X * L ≤ (m : ℝ) := by
        have hfactor :
            lam * (μ₁ ^ 2) * ((N : ℝ) * (r : ℝ) * L) ≤
              lam * (μ₁ * A) * ((N : ℝ) * (r : ℝ) * L) := by
          have hlam_nonneg : 0 ≤ lam := le_of_lt hlam_pos
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hmuA_ge_musq hlam_nonneg)
            htail_nonneg
        have hmLower' :
            (m : ℝ) ≥ lam * μ₁ * A * (N : ℝ) * (r : ℝ) * L := by
          simpa [N, A, L, mul_assoc] using hmLower
        nlinarith
      have hm_pos_real : 0 < (m : ℝ) := by
        have hsample_pos : 0 < lam * X * L := by
          have hX_pos : 0 < X := by
            dsimp [X]
            positivity
          positivity
        exact lt_of_lt_of_le hsample_pos hsample_core
      have hm_pos_nat : 0 < m := Nat.cast_pos.mp hm_pos_real
      have hratio_sample :
          X / (m : ℝ) ≤ (lam * L)⁻¹ := by
        rw [← one_div]
        rw [div_le_div_iff₀ hm_pos_real (mul_pos hlam_pos hL_pos)]
        nlinarith [hsample_core]
      have hlam_log2_pos : 0 < lam * Real.log (2 : ℝ) := mul_pos hlam_pos hlog2_pos
      have hlam_L_pos : 0 < lam * L := mul_pos hlam_pos hL_pos
      have hlam_log2_le_lam_L : lam * Real.log (2 : ℝ) ≤ lam * L :=
        mul_le_mul_of_nonneg_left hL_ge_log2 (le_of_lt hlam_pos)
      have hinv_L_le_inv_log2 :
          (lam * L)⁻¹ ≤ (lam * Real.log (2 : ℝ))⁻¹ := by
        rw [inv_le_inv₀ hlam_L_pos hlam_log2_pos]
        exact hlam_log2_le_lam_L
      have hX_over_m_le :
          X / (m : ℝ) ≤ (lam * Real.log (2 : ℝ))⁻¹ :=
        le_trans hratio_sample hinv_L_le_inv_log2
      have hshape :
          ((n₁ : ℝ) * (n₂ : ℝ)) / (((min n₁ n₂ : ℕ) : ℝ)) ≤ (N : ℝ) := by
        simpa [N] using rectangular_cardinality_div_min_le_max hn₁ hn₂
      have hp_inv_bound :=
        sample_ratio_inverse_one_minus_le_card_div_sample hn₁ hn₂ hm hm_pos_nat
      have hdensity_energy_le :
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹ *
              (1 - ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
            (μ₁ ^ 2 * (r : ℝ) / (↑(min n₁ n₂))) ≤
            X / (m : ℝ) := by
        have henergy_nonneg :
            0 ≤ μ₁ ^ 2 * (r : ℝ) / (↑(min n₁ n₂) : ℝ) := by
          positivity
        have hstep₁ :
            ((((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹ *
                (1 - ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))) *
              (μ₁ ^ 2 * (r : ℝ) / (↑(min n₁ n₂) : ℝ))) ≤
              (((n₁ : ℝ) * (n₂ : ℝ)) / (m : ℝ)) *
                (μ₁ ^ 2 * (r : ℝ) / (↑(min n₁ n₂) : ℝ)) := by
          exact mul_le_mul_of_nonneg_right hp_inv_bound henergy_nonneg
        have hstep₂ :
            (((n₁ : ℝ) * (n₂ : ℝ)) / (m : ℝ)) *
                (μ₁ ^ 2 * (r : ℝ) / (↑(min n₁ n₂) : ℝ)) ≤
              X / (m : ℝ) := by
          have hscale :
              μ₁ ^ 2 * (r : ℝ) *
                  (((n₁ : ℝ) * (n₂ : ℝ)) / (↑(min n₁ n₂) : ℝ)) ≤
                μ₁ ^ 2 * (r : ℝ) * (N : ℝ) := by
            have hcoef_nonneg : 0 ≤ μ₁ ^ 2 * (r : ℝ) := by positivity
            exact mul_le_mul_of_nonneg_left hshape hcoef_nonneg
          have hleft_eq :
              ((((n₁ : ℝ) * (n₂ : ℝ)) / (m : ℝ)) *
                  (μ₁ ^ 2 * (r : ℝ) / (↑(min n₁ n₂) : ℝ))) *
                  (m : ℝ) =
                μ₁ ^ 2 * (r : ℝ) *
                  (((n₁ : ℝ) * (n₂ : ℝ)) / (↑(min n₁ n₂) : ℝ)) := by
            field_simp [hm_pos_real.ne', hmin_pos.ne']
          have hright_eq :
              (X / (m : ℝ)) * (m : ℝ) =
                μ₁ ^ 2 * (r : ℝ) * (N : ℝ) := by
            field_simp [X, hm_pos_real.ne']
            ring
          have hmul :
              ((((n₁ : ℝ) * (n₂ : ℝ)) / (m : ℝ)) *
                  (μ₁ ^ 2 * (r : ℝ) / (↑(min n₁ n₂) : ℝ))) *
                  (m : ℝ) ≤
                (X / (m : ℝ)) * (m : ℝ) := by
            calc
              ((((n₁ : ℝ) * (n₂ : ℝ)) / (m : ℝ)) *
                    (μ₁ ^ 2 * (r : ℝ) / (↑(min n₁ n₂) : ℝ))) *
                    (m : ℝ)
                  = μ₁ ^ 2 * (r : ℝ) *
                      (((n₁ : ℝ) * (n₂ : ℝ)) / (↑(min n₁ n₂) : ℝ)) := hleft_eq
              _ ≤ μ₁ ^ 2 * (r : ℝ) * (N : ℝ) := hscale
              _ = (X / (m : ℝ)) * (m : ℝ) := hright_eq.symm
          exact (mul_le_mul_iff_of_pos_right hm_pos_real).mp hmul
        exact le_trans hstep₁ hstep₂
      have hleft_le :
          Cdiag *
              (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹ *
                  (1 - ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                (μ₁ ^ 2 * (r : ℝ) / (↑(min n₁ n₂)))) ≤
            Cdiag * (X / (m : ℝ)) :=
        mul_le_mul_of_nonneg_left hdensity_energy_le hCdiag_nonneg
      have hright_scale :
          Cdiag * (X / (m : ℝ)) ≤
            (Cdiag * (Real.log (2 : ℝ))⁻¹) * Real.rpow lam (-1) := by
        rw [hRpow]
        have htmp :
            Cdiag * (X / (m : ℝ)) ≤
              Cdiag * ((lam * Real.log (2 : ℝ))⁻¹) :=
          mul_le_mul_of_nonneg_left hX_over_m_le hCdiag_nonneg
        simpa [mul_assoc, mul_left_comm, mul_comm] using htmp
      exact le_trans hleft_le hright_scale
