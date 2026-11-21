-- Prove2me | solution 1 for P2M_Mpfx_next_extend_midpoint__cd09fcf4dbfc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:57:21.528322+00:00
-- url     : https://prove2.me/submissions/b13b1329-d685-4e57-9b5b-17c3a1108cab

import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Mpfx_Format_Next
import Theorems.Thm_Mpfx_Format_withBound_p
import Theorems.Thm_Mpfx_Format_withBound_exp
import Theorems.Thm_Mpfx_Format_withBound_b
import Theorems.Thm_Mpfx_Format_withBound_specials
import Theorems.Thm_Mpfx_Format_next_zero
import Theorems.Thm_Mpfx_Format_boundAfterNext_top
import Theorems.Thm_Mpfx_FiniteFormat_next_eq_format_next
import Theorems.Thm_Mpfx_Dyadic_coe_abs
import Theorems.Thm_Mpfx_Dyadic_coe_half
import Theorems.Thm_Mpfx_Dyadic_coe_ofIntZpow
import Theorems.Thm_Mpfx_Dyadic_coe_rat_abs
import Theorems.Thm_Mpfx_Dyadic_coe_rat_half
import Theorems.Thm_Mpfx_Dyadic_coe_rat_ofIntZpow
import Theorems.Thm_Mpfx_Dyadic_coe_real_add
import Theorems.Thm_Mpfx_Dyadic_coe_real_inj
import Theorems.Thm_Mpfx_Dyadic_coe_real_mul
import Theorems.Thm_Mpfx_Dyadic_coe_real_neg
import Theorems.Thm_Mpfx_Dyadic_coe_real_sub
import Theorems.Thm_Mpfx_Dyadic_coe_real_zero
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_neg_iff
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_top
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_bot
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_neg_iff
import Theorems.Thm_Mpfx_FiniteFormat_canonicalExp_extend
import Theorems.Thm_Mpfx_FiniteFormat_extend_toFormat
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_b
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_canonicalExp
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_exp
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_p
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_toFormat
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_unbounded
import Theorems.Thm_Mpfx_Format_boundOK_neg_iff
import Theorems.Thm_Mpfx_Format_boundOK_zero
import Theorems.Thm_Mpfx_Format_extend_exp_coe
import Theorems.Thm_Mpfx_Format_finite_mem_values
import Theorems.Thm_Mpfx_Format_special_mem_values
import Theorems.Thm_Mpfx_Format_unbounded_b
import Theorems.Thm_Mpfx_Format_unbounded_exp
import Theorems.Thm_Mpfx_Format_unbounded_p
import Theorems.Thm_Mpfx_Format_unbounded_specials
import Theorems.Thm_Mpfx_Format_unbounded_unbounded
import Theorems.Thm_Mpfx_Special_neg_neg
import Theorems.Thm_Mpfx_WithSpecial_neg_finite
import Theorems.Thm_Mpfx_WithSpecial_neg_neg
import Theorems.Thm_Mpfx_WithSpecial_neg_special
import Theorems.Thm_Mpfx_WithSpecial_toReal_finite
import Theorems.Thm_Mpfx_WithSpecial_toReal_special
import Theorems.Thm_Mpfx_coe_real_ofIntZpow_one
import Theorems.Thm_Mpfx_eq_zero_of_coe_real_zero
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


attribute [local simp] Mpfx.Format.withBound_p
attribute [local simp] Mpfx.Format.withBound_exp
attribute [local simp] Mpfx.Format.withBound_b
attribute [local simp] Mpfx.Format.withBound_specials
attribute [local simp] Mpfx.Format.boundAfterNext_top
section
namespace Mpfx
namespace Format
end Format
namespace FiniteFormat
private theorem next_of_ne (F : FiniteFormat) {b : _root_.Mpfx.Dyadic}
    (h : ¬(((b : _root_.Mpfx.Dyadic) : ℝ) = 0 ∧ F.exp = ⊥)) :
    F.next b = b + _root_.Mpfx.Dyadic.ofIntZpow 1 (F.canonicalExp ((b : _root_.Mpfx.Dyadic) : ℝ)) := if_neg h
end FiniteFormat
private theorem coe_add_ulp_halves {b : _root_.Mpfx.Dyadic} (t : ℤ) :
    ((b + _root_.Mpfx.Dyadic.ofIntZpow 1 (t - 1) : _root_.Mpfx.Dyadic) : ℝ)
      = (((b : _root_.Mpfx.Dyadic) : ℝ) + ((b + _root_.Mpfx.Dyadic.ofIntZpow 1 t : _root_.Mpfx.Dyadic) : ℝ)) / 2 := by
  rw [_root_.Mpfx.Dyadic.coe_real_add, _root_.Mpfx.Dyadic.coe_real_add, coe_real_ofIntZpow_one,
    coe_real_ofIntZpow_one, zpow_sub_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
  ring
private theorem next_pos_eq (F : FiniteFormat) {b : _root_.Mpfx.Dyadic} (hb : 0 < ((b : _root_.Mpfx.Dyadic) : ℝ)) :
    F.toFormat.next b = b + _root_.Mpfx.Dyadic.ofIntZpow 1 (F.canonicalExp ((b : _root_.Mpfx.Dyadic) : ℝ)) := by
  rw [FiniteFormat.next_eq_format_next F hb,
    FiniteFormat.next_of_ne F (by simp [ne_of_gt hb])]
end Mpfx
end

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F₁ : FiniteFormat} {b : _root_.Mpfx.Dyadic}
    (hb_nn : 0 ≤ ((b : _root_.Mpfx.Dyadic) : ℝ))
    (hguard : F₁.exp = ⊥ → 0 < ((b : _root_.Mpfx.Dyadic) : ℝ)) :
    (((F₁.extend 1).toFormat.next b : _root_.Mpfx.Dyadic) : ℝ)
      = (((b : _root_.Mpfx.Dyadic) : ℝ) + ((F₁.toFormat.next b : _root_.Mpfx.Dyadic) : ℝ)) / 2 := by
  rcases eq_or_lt_of_le hb_nn with hb0 | hb0
  · -- `b = 0`: both steps are pure powers of two, one bit apart
    have hbz : b = 0 :=
      eq_zero_of_coe_real_zero hb0.symm
    cases he : F₁.exp using QExp.recBotCoe with
    | bot => exact absurd (hguard he) (by rw [← hb0]; exact lt_irrefl 0)
    | coe e =>
      have hex : (F₁.extend 1).exp = ((e - 1 : ℤ) : QExp) := Format.extend_exp_coe he 1
      have hzero : ∀ (G : FiniteFormat) {q : ℤ}, G.exp = (q : QExp) →
          G.toFormat.next b = _root_.Mpfx.Dyadic.ofIntZpow 1 q := by
        intro G q hq
        rw [hbz]; exact Format.next_zero _ hq
      rw [hzero (F₁.extend 1) hex, hzero F₁ he, coe_real_ofIntZpow_one,
        coe_real_ofIntZpow_one, ← hb0, zpow_sub_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
      ring
  · -- `b > 0`: the step exponent drops by exactly one
    rw [next_pos_eq (F₁.extend 1) hb0, next_pos_eq F₁ hb0,
      F₁.canonicalExp_extend 1 (ne_of_gt hb0)]
    exact coe_add_ulp_halves _
end Mpfx
