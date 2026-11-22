-- Prove2me | solution 1 for Mpfx.two_le_p_or_trivial_of_extend_one_withBound_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:00:25.633081+00:00
-- url     : https://prove2.me/submissions/7a680628-798d-4784-b0c4-2adfa4c5abb9

import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Mpfx_Format_Next
import Theorems.Thm_Mpfx_Format_withBound_p
import Theorems.Thm_Mpfx_Format_withBound_exp
import Theorems.Thm_Mpfx_Format_withBound_b
import Theorems.Thm_Mpfx_Format_withBound_specials
import Theorems.Thm_Mpfx_Format_boundAfterNext_top
import Theorems.Thm_Mpfx_FiniteFormat_format_next_eq
import Theorems.Thm_Mpfx_next_mono
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
import Theorems.Thm_Mpfx_Dyadic_not_precisionAtMost_one_three_zpow
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_mono
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_neg_iff
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_top
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_two_three_zpow
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_bot
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_neg_iff
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_ofIntZpow
import Theorems.Thm_Mpfx_FiniteFormat_exists_mul_zpow_canonicalExp
import Theorems.Thm_Mpfx_FiniteFormat_exp_le_canonicalExp
import Theorems.Thm_Mpfx_FiniteFormat_extend_toFormat
import Theorems.Thm_Mpfx_FiniteFormat_neg_mem
import Theorems.Thm_Mpfx_FiniteFormat_p_pos
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_b
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_canonicalExp
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_exp
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_p
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_toFormat
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_unbounded
import Theorems.Thm_Mpfx_Format_boundOK_neg_iff
import Theorems.Thm_Mpfx_Format_boundOK_zero
import Theorems.Thm_Mpfx_Format_extend_exp_bot
import Theorems.Thm_Mpfx_Format_extend_exp_coe
import Theorems.Thm_Mpfx_Format_finite_mem_values
import Theorems.Thm_Mpfx_Format_neg_mem
import Theorems.Thm_Mpfx_Format_special_mem_values
import Theorems.Thm_Mpfx_Format_two_le_p_of_precision_two_witness
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
import Theorems.Thm_Mpfx_abs_coe_real_le_of_boundOK
import Theorems.Thm_Mpfx_boundOK_coe_of_abs_le
import Theorems.Thm_Mpfx_coe_real_ofIntZpow_one
import Theorems.Thm_Mpfx_mem_unbounded_of_mem
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
private theorem boundAfterNext_coe {F : Format} {b : NonNegDyadic} (hF : F.b = (b : Bound)) :
    ∃ h, F.boundAfterNext = ((⟨F.next b.val, h⟩ : NonNegDyadic) : Bound) := by
  unfold boundAfterNext; rw [hF]; exact ⟨_, rfl⟩
end Format
namespace FiniteFormat
end FiniteFormat
end Mpfx
end

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat) :
    ((2 : ℕ) : Prec) ≤ F₂.p ∨ ∀ d : _root_.Mpfx.Dyadic, d ∈ F₁ → (d : ℝ) = 0 := by
  by_contra h
  push Not at h
  obtain ⟨h_p_lt, ⟨d₀, hd₀_mem, hd₀_ne⟩⟩ := h
  obtain ⟨d, hd_mem, hd_pos⟩ : ∃ d : _root_.Mpfx.Dyadic, d ∈ F₁ ∧ (0 : ℝ) < d := by
    rcases hd₀_ne.lt_or_gt with h | h
    · exact ⟨-d₀, FiniteFormat.neg_mem hd₀_mem, by rw [_root_.Mpfx.Dyadic.coe_real_neg]; linarith⟩
    · exact ⟨d₀, hd₀_mem, h⟩
  set c := F₁.canonicalExp (d : ℝ)
  -- `d = m · 2^c` with `m ≥ 1`, so `2^c ≤ d`.
  obtain ⟨m, hm⟩ := F₁.exists_mul_zpow_canonicalExp (mem_unbounded_of_mem hd_mem)
  have h2c : (0 : ℝ) < (2 : ℝ) ^ c := zpow_pos two_pos c
  have hd_ge : (2 : ℝ) ^ c ≤ d := by
    have hm0 : (0 : ℝ) < m := pos_of_mul_pos_left (hm ▸ hd_pos) h2c.le
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show (0 : ℤ) < m by exact_mod_cast hm0)
    rw [hm]; nlinarith
  have hp_ext : ((2 : ℕ) : Prec) ≤ (F₁.extend 1).p := by
    change ((2 : ℕ) : Prec) ≤ F₁.p + ((1 : ℕ) : Prec)
    cases hp : F₁.p using ENat.recTopCoe with
    | top => simp
    | coe n => rw [← Nat.cast_add]; exact ENat.coe_le_coe.mpr (Nat.succ_le_succ (F₁.p_pos hp))
  refine absurd (Format.two_le_p_of_precision_two_witness (hsub (_root_.Mpfx.Dyadic.ofIntZpow 3 (c - 1))
    ⟨_root_.Mpfx.Dyadic.precisionAtMost_mono hp_ext (_root_.Mpfx.Dyadic.precisionAtMost_two_three_zpow _),
      _root_.Mpfx.Dyadic.quantumAtLeast_ofIntZpow ?_, ?_⟩)
    (_root_.Mpfx.Dyadic.not_precisionAtMost_one_three_zpow _)) (not_le.mpr h_p_lt)
  · change (F₁.toFormat.extend 1).exp ≤ _
    cases he : F₁.exp using QExp.recBotCoe with
    | bot => rw [Format.extend_exp_bot he]; exact bot_le
    | coe e =>
      rw [Format.extend_exp_coe he]
      exact WithBot.coe_le_coe.mpr (by have := F₁.exp_le_canonicalExp (d : ℝ) he; omega)
  · change Format.boundOK F₁.toFormat.boundAfterNext _
    rcases hF_b : F₁.b with _ | b
    · rw [Format.boundAfterNext_top hF_b]; trivial
    obtain ⟨_, h_bAfter⟩ := Format.boundAfterNext_coe hF_b
    rw [h_bAfter]
    refine boundOK_coe_of_abs_le ?_
    -- `|3 · 2^(c−1)| ≤ 2^c + 2^c ≤ d + 2^c = next d ≤ next b`.
    have hdb : (d : ℝ) ≤ (b.val : ℝ) := by
      have h := hd_mem.2.2
      rw [hF_b] at h
      exact (le_abs_self _).trans (abs_coe_real_le_of_boundOK h)
    have hmono := next_mono (F := F₁) hd_pos.le hdb fun _ => hd_pos
    rw [F₁.format_next_eq hd_pos.le fun _ => hd_pos, _root_.Mpfx.Dyadic.coe_real_add,
      coe_real_ofIntZpow_one] at hmono
    have hc1 : (2 : ℝ) ^ (c - 1) ≤ (2 : ℝ) ^ c := zpow_le_zpow_right₀ (by norm_num) (by omega)
    have hv : ((_root_.Mpfx.Dyadic.ofIntZpow 3 (c - 1) : _root_.Mpfx.Dyadic) : ℝ) = (2 : ℝ) ^ c + (2 : ℝ) ^ (c - 1) := by
      rw [_root_.Mpfx.Dyadic.coe_ofIntZpow, zpow_sub_one₀ two_ne_zero]; push_cast; ring
    rw [hv, abs_of_pos (by positivity)]
    linarith
end Mpfx
