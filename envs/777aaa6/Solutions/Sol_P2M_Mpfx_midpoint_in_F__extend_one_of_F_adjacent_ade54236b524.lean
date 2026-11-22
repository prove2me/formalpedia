-- Prove2me | solution 1 for P2M_Mpfx_midpoint_in_F__extend_one_of_F_adjacent_ade54236b524
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:01:49.280816+00:00
-- url     : https://prove2.me/submissions/b3fee649-4a31-45a0-9e00-3c0f4576e89c

import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Mpfx_Format_Discrete
import Theorems.Thm_Mpfx_midpoint_mem_extend_one_of_adjacent_pos
import Theorems.Thm_Mpfx_Dyadic_coe_abs
import Theorems.Thm_Mpfx_Dyadic_coe_half
import Theorems.Thm_Mpfx_Dyadic_coe_midpoint
import Theorems.Thm_Mpfx_Dyadic_coe_ofIntZpow
import Theorems.Thm_Mpfx_Dyadic_coe_rat_abs
import Theorems.Thm_Mpfx_Dyadic_coe_rat_half
import Theorems.Thm_Mpfx_Dyadic_coe_rat_midpoint
import Theorems.Thm_Mpfx_Dyadic_coe_rat_ofIntZpow
import Theorems.Thm_Mpfx_Dyadic_coe_real_add
import Theorems.Thm_Mpfx_Dyadic_coe_real_inj
import Theorems.Thm_Mpfx_Dyadic_coe_real_mul
import Theorems.Thm_Mpfx_Dyadic_coe_real_neg
import Theorems.Thm_Mpfx_Dyadic_coe_real_sub
import Theorems.Thm_Mpfx_Dyadic_coe_real_zero
import Theorems.Thm_Mpfx_Dyadic_ext_real
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_coe
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_mono
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_neg_iff
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_top
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_bot
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_coe
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_neg_iff
import Theorems.Thm_Mpfx_FiniteFormat_extend_toFormat
import Theorems.Thm_Mpfx_FiniteFormat_neg_mem
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_b
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_canonicalExp
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_exp
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_p
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_toFormat
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_unbounded
import Theorems.Thm_Mpfx_FiniteFormat_zero_mem
import Theorems.Thm_Mpfx_Format_boundOK_neg_iff
import Theorems.Thm_Mpfx_Format_boundOK_zero
import Theorems.Thm_Mpfx_Format_finite_mem_values
import Theorems.Thm_Mpfx_Format_neg_mem
import Theorems.Thm_Mpfx_Format_special_mem_values
import Theorems.Thm_Mpfx_Format_unbounded_b
import Theorems.Thm_Mpfx_Format_unbounded_exp
import Theorems.Thm_Mpfx_Format_unbounded_p
import Theorems.Thm_Mpfx_Format_unbounded_specials
import Theorems.Thm_Mpfx_Format_unbounded_unbounded
import Theorems.Thm_Mpfx_Format_zero_mem
import Theorems.Thm_Mpfx_Special_neg_neg
import Theorems.Thm_Mpfx_WithSpecial_neg_finite
import Theorems.Thm_Mpfx_WithSpecial_neg_neg
import Theorems.Thm_Mpfx_WithSpecial_neg_special
import Theorems.Thm_Mpfx_WithSpecial_toReal_finite
import Theorems.Thm_Mpfx_WithSpecial_toReal_special
attribute [local simp] Mpfx.Dyadic.coe_abs
attribute [local simp] Mpfx.Dyadic.coe_half
attribute [local simp] Mpfx.Dyadic.coe_ofIntZpow
attribute [local simp] Mpfx.Dyadic.coe_rat_abs
attribute [local simp] Mpfx.Dyadic.coe_rat_half
attribute [local simp] Mpfx.Dyadic.coe_rat_ofIntZpow
attribute [local simp] Mpfx.Dyadic.coe_real_add
attribute [local simp] Mpfx.Dyadic.coe_real_inj
attribute [local simp] Mpfx.Dyadic.coe_real_mul
attribute [local simp] Mpfx.Dyadic.coe_real_neg
attribute [local simp] Mpfx.Dyadic.coe_real_sub
attribute [local simp] Mpfx.Dyadic.coe_real_zero
attribute [local simp] Mpfx.Dyadic.precisionAtMost_neg_iff
attribute [local simp] Mpfx.Dyadic.precisionAtMost_top
attribute [local simp] Mpfx.Dyadic.quantumAtLeast_bot
attribute [local simp] Mpfx.Dyadic.quantumAtLeast_neg_iff
attribute [local simp] Mpfx.FiniteFormat.extend_toFormat
attribute [local simp] Mpfx.FiniteFormat.unbounded_b
attribute [local simp] Mpfx.FiniteFormat.unbounded_canonicalExp
attribute [local simp] Mpfx.FiniteFormat.unbounded_exp
attribute [local simp] Mpfx.FiniteFormat.unbounded_p
attribute [local simp] Mpfx.FiniteFormat.unbounded_toFormat
attribute [local simp] Mpfx.FiniteFormat.unbounded_unbounded
attribute [local simp] Mpfx.Format.boundOK_neg_iff
attribute [local simp] Mpfx.Format.boundOK_zero
attribute [local simp] Mpfx.Format.finite_mem_values
attribute [local simp] Mpfx.Format.special_mem_values
attribute [local simp] Mpfx.Format.unbounded_b
attribute [local simp] Mpfx.Format.unbounded_exp
attribute [local simp] Mpfx.Format.unbounded_p
attribute [local simp] Mpfx.Format.unbounded_specials
attribute [local simp] Mpfx.Format.unbounded_unbounded
attribute [local simp] Mpfx.Special.neg_neg
attribute [local simp] Mpfx.WithSpecial.neg_finite
attribute [local simp] Mpfx.WithSpecial.neg_neg
attribute [local simp] Mpfx.WithSpecial.neg_special
attribute [local simp] Mpfx.WithSpecial.toReal_finite
attribute [local simp] Mpfx.WithSpecial.toReal_special


section
namespace Mpfx
private theorem boundOK_midpoint {B : Bound} {y₁ y₂ : _root_.Mpfx.Dyadic}
    (h₁ : Format.boundOK B y₁) (h₂ : Format.boundOK B y₂) :
    Format.boundOK B (_root_.Mpfx.Dyadic.midpoint y₁ y₂) := by
  cases B using Bound.recTopCoe with
  | top => trivial
  | coe B =>
    change |((_root_.Mpfx.Dyadic.midpoint y₁ y₂ : _root_.Mpfx.Dyadic) : ℚ)| ≤ ((B.val : _root_.Mpfx.Dyadic) : ℚ)
    change |((y₁ : _root_.Mpfx.Dyadic) : ℚ)| ≤ ((B.val : _root_.Mpfx.Dyadic) : ℚ) at h₁
    change |((y₂ : _root_.Mpfx.Dyadic) : ℚ)| ≤ ((B.val : _root_.Mpfx.Dyadic) : ℚ) at h₂
    rw [_root_.Mpfx.Dyadic.coe_rat_midpoint, abs_div, abs_of_pos (by norm_num : (0 : ℚ) < 2)]
    have h_tri : |((y₁ : _root_.Mpfx.Dyadic) : ℚ) + ((y₂ : _root_.Mpfx.Dyadic) : ℚ)|
        ≤ |((y₁ : _root_.Mpfx.Dyadic) : ℚ)| + |((y₂ : _root_.Mpfx.Dyadic) : ℚ)| := abs_add_le _ _
    linarith
private theorem half_mem_extend_one (F : FiniteFormat)
    {y : _root_.Mpfx.Dyadic} (hyF : y ∈ F) :
    (_root_.Mpfx.Dyadic.midpoint 0 y : _root_.Mpfx.Dyadic) ∈ F.extend 1 := by
  obtain ⟨hp_y, hq_y, hb_y⟩ := hyF
  have h_mid_eq : ((_root_.Mpfx.Dyadic.midpoint 0 y : _root_.Mpfx.Dyadic) : ℝ) = ((y : _root_.Mpfx.Dyadic) : ℝ) / 2 := by
    rw [_root_.Mpfx.Dyadic.coe_midpoint]; push_cast; ring
  have h_mid_eq_rat : ((_root_.Mpfx.Dyadic.midpoint 0 y : _root_.Mpfx.Dyadic) : ℚ) = ((y : _root_.Mpfx.Dyadic) : ℚ) / 2 := by
    rw [_root_.Mpfx.Dyadic.coe_rat_midpoint]; push_cast; ring
  refine ⟨?_, ?_, ?_⟩
  · -- Halving keeps the significand, so the precision is unchanged.
    change _root_.Mpfx.Dyadic.precisionAtMost (F.p + ((1 : ℕ) : Prec)) _
    refine _root_.Mpfx.Dyadic.precisionAtMost_mono (le_add_right le_rfl) ?_
    cases hpF : F.p using ENat.recTopCoe with
    | top => trivial
    | coe p =>
      have hp_y' : _root_.Mpfx.Dyadic.precisionAtMost (p : Prec) y := hpF ▸ hp_y
      rw [_root_.Mpfx.Dyadic.precisionAtMost_coe] at hp_y' ⊢
      obtain ⟨c, e, hy_eq, hc_lt⟩ := hp_y'
      refine ⟨c, e - 1, ?_, hc_lt⟩
      rw [h_mid_eq_rat, hy_eq, zpow_sub₀ (by norm_num : (2 : ℚ) ≠ 0)]
      field_simp
  · show _root_.Mpfx.Dyadic.quantumAtLeast (F.extend 1).exp _
    have h_exp_eq : (F.extend 1).exp = F.exp.map (· - ((1 : ℕ) : ℤ)) := rfl
    rw [h_exp_eq]
    cases hF_exp : F.exp using QExp.recBotCoe with
    | bot => trivial
    | coe e =>
      rw [WithBot.map_coe]
      change _root_.Mpfx.Dyadic.quantumAtLeast (((e - (1 : ℕ)) : ℤ) : QExp) _
      rw [_root_.Mpfx.Dyadic.quantumAtLeast_coe]
      rw [hF_exp] at hq_y
      rw [_root_.Mpfx.Dyadic.quantumAtLeast_coe] at hq_y
      obtain ⟨c, hy_eq⟩ := hq_y
      refine ⟨c, ?_⟩
      rw [h_mid_eq_rat, hy_eq]
      have : ((1 : ℕ) : ℤ) = 1 := rfl
      rw [this, zpow_sub₀ (by norm_num : (2 : ℚ) ≠ 0)]
      field_simp
  · exact boundOK_midpoint (Format.boundOK_zero F.b) hb_y
end Mpfx
end

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F : FiniteFormat}
    {y₁ y₂ : _root_.Mpfx.Dyadic} (hy₁F : y₁ ∈ F) (hy₂F : y₂ ∈ F)
    (h_lt : ((y₁ : _root_.Mpfx.Dyadic) : ℝ) < ((y₂ : _root_.Mpfx.Dyadic) : ℝ))
    (h_adj : ∀ y : _root_.Mpfx.Dyadic, y ∈ F →
              ((y₁ : _root_.Mpfx.Dyadic) : ℝ) < ((y : _root_.Mpfx.Dyadic) : ℝ) →
              ((y₂ : _root_.Mpfx.Dyadic) : ℝ) ≤ ((y : _root_.Mpfx.Dyadic) : ℝ)) :
    _root_.Mpfx.Dyadic.midpoint y₁ y₂ ∈ F.extend 1 := by
  rcases lt_trichotomy ((y₁ : _root_.Mpfx.Dyadic) : ℝ) 0 with hy₁_neg | hy₁_zero | hy₁_pos
  · rcases lt_trichotomy ((y₂ : _root_.Mpfx.Dyadic) : ℝ) 0 with hy₂_neg | hy₂_zero | hy₂_pos
    · -- Both negative: apply the positive case to `(-y₂, -y₁)`.
      have h_neg_y₁_pos : 0 < ((-y₁ : _root_.Mpfx.Dyadic) : ℝ) := by push_cast; linarith
      have h_neg_y₂_pos : 0 < ((-y₂ : _root_.Mpfx.Dyadic) : ℝ) := by push_cast; linarith
      have h_lt' : ((-y₂ : _root_.Mpfx.Dyadic) : ℝ) < ((-y₁ : _root_.Mpfx.Dyadic) : ℝ) := by push_cast; linarith
      have h_adj' : ∀ y : _root_.Mpfx.Dyadic, y ∈ F →
          ((-y₂ : _root_.Mpfx.Dyadic) : ℝ) < ((y : _root_.Mpfx.Dyadic) : ℝ) →
          ((-y₁ : _root_.Mpfx.Dyadic) : ℝ) ≤ ((y : _root_.Mpfx.Dyadic) : ℝ) := by
        intro y hyF hyg
        by_contra h_lt_neg
        push Not at h_lt_neg
        have h_neg_yF : -y ∈ F := FiniteFormat.neg_mem hyF
        have h_y_gt_y₁ : ((y₁ : _root_.Mpfx.Dyadic) : ℝ) < ((-y : _root_.Mpfx.Dyadic) : ℝ) := by
          push_cast at h_lt_neg ⊢; linarith
        have h_y_le_y₂ := h_adj (-y) h_neg_yF h_y_gt_y₁
        push_cast at hyg h_y_le_y₂
        linarith
      have h_neg_in_extend := midpoint_mem_extend_one_of_adjacent_pos F
        (FiniteFormat.neg_mem hy₂F) (FiniteFormat.neg_mem hy₁F)
        h_neg_y₂_pos h_lt' h_adj'
      have h_mid_neg : _root_.Mpfx.Dyadic.midpoint (-y₂) (-y₁) = -(_root_.Mpfx.Dyadic.midpoint y₁ y₂) := by
        apply _root_.Mpfx.Dyadic.ext_real
        simp only [_root_.Mpfx.Dyadic.coe_midpoint, _root_.Mpfx.Dyadic.coe_real_neg]
        ring
      rw [h_mid_neg] at h_neg_in_extend
      have := FiniteFormat.neg_mem h_neg_in_extend
      rw [neg_neg] at this
      exact this
    · -- `y₂ = 0`: halve `-y₁`.
      have h_y₂_eq_0 : y₂ = 0 := _root_.Mpfx.Dyadic.ext_real (by rw [_root_.Mpfx.Dyadic.coe_real_zero]; exact hy₂_zero)
      rw [h_y₂_eq_0]
      have h_mid_eq : _root_.Mpfx.Dyadic.midpoint y₁ 0 = -(_root_.Mpfx.Dyadic.midpoint 0 (-y₁)) := by
        apply _root_.Mpfx.Dyadic.ext_real
        simp only [_root_.Mpfx.Dyadic.coe_midpoint, _root_.Mpfx.Dyadic.coe_real_neg]
        push_cast; ring
      rw [h_mid_eq]
      have h_neg_y₁F : -y₁ ∈ F := FiniteFormat.neg_mem hy₁F
      have h_half := half_mem_extend_one F h_neg_y₁F
      exact FiniteFormat.neg_mem h_half
    · -- `y₁ < 0 < y₂` contradicts adjacency, since `0 ∈ F`.
      exfalso
      have h_0_F : (0 : _root_.Mpfx.Dyadic) ∈ F := FiniteFormat.zero_mem F
      have h_0_gt : ((y₁ : _root_.Mpfx.Dyadic) : ℝ) < ((0 : _root_.Mpfx.Dyadic) : ℝ) := by
        rw [_root_.Mpfx.Dyadic.coe_real_zero]; exact hy₁_neg
      have h_y₂_le : ((y₂ : _root_.Mpfx.Dyadic) : ℝ) ≤ ((0 : _root_.Mpfx.Dyadic) : ℝ) := h_adj 0 h_0_F h_0_gt
      rw [_root_.Mpfx.Dyadic.coe_real_zero] at h_y₂_le
      linarith
  · have h_y₁_eq_0 : y₁ = 0 := _root_.Mpfx.Dyadic.ext_real (by rw [_root_.Mpfx.Dyadic.coe_real_zero]; exact hy₁_zero)
    rw [h_y₁_eq_0]
    exact half_mem_extend_one F hy₂F
  · exact midpoint_mem_extend_one_of_adjacent_pos F hy₁F hy₂F hy₁_pos h_lt h_adj
end Mpfx
