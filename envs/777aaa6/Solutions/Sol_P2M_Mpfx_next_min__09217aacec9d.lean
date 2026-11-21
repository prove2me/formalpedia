-- Prove2me | solution 1 for P2M_Mpfx_next_min__09217aacec9d
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:54:40.600728+00:00
-- url     : https://prove2.me/submissions/bc2bf6ad-8f57-4e55-95db-22258b780e57

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
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_coe_real
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_neg_iff
import Theorems.Thm_Mpfx_FiniteFormat_canonicalExp_mono
import Theorems.Thm_Mpfx_FiniteFormat_exists_mul_zpow_canonicalExp
import Theorems.Thm_Mpfx_FiniteFormat_extend_toFormat
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_b
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_canonicalExp
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_exp
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_p
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_toFormat
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_unbounded
import Theorems.Thm_Mpfx_Format_boundOK_neg_iff
import Theorems.Thm_Mpfx_Format_boundOK_zero
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
import Theorems.Thm_Mpfx_int_mul_two_zpow_le_iff
import Theorems.Thm_Mpfx_int_mul_two_zpow_lt_iff
import Theorems.Thm_Mpfx_two_zpow_split_toNat
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
private theorem next_ulp_min {F : Format} {b g : _root_.Mpfx.Dyadic} {mb mg s : ℤ}
    (hmb : ((b : _root_.Mpfx.Dyadic) : ℝ) = (mb : ℝ) * (2 : ℝ) ^ s)
    (hmg : ((g : _root_.Mpfx.Dyadic) : ℝ) = (mg : ℝ) * (2 : ℝ) ^ s)
    (hbg : ((b : _root_.Mpfx.Dyadic) : ℝ) < ((g : _root_.Mpfx.Dyadic) : ℝ))
    (h_next : F.next b = b + _root_.Mpfx.Dyadic.ofIntZpow 1 s) :
    ((F.next b : _root_.Mpfx.Dyadic) : ℝ) ≤ ((g : _root_.Mpfx.Dyadic) : ℝ) := by
  rw [hmb, hmg] at hbg
  have hm_lt := int_mul_two_zpow_lt_iff.mp hbg
  rw [h_next, _root_.Mpfx.Dyadic.coe_real_add, coe_real_ofIntZpow_one s, hmb, hmg]
  have h := int_mul_two_zpow_le_iff (k := s).mpr (show mb + 1 ≤ mg by omega)
  push_cast at h
  linarith
private theorem next_pos_eq (F : FiniteFormat) {b : _root_.Mpfx.Dyadic} (hb : 0 < ((b : _root_.Mpfx.Dyadic) : ℝ)) :
    F.toFormat.next b = b + _root_.Mpfx.Dyadic.ofIntZpow 1 (F.canonicalExp ((b : _root_.Mpfx.Dyadic) : ℝ)) := by
  rw [FiniteFormat.next_eq_format_next F hb,
    FiniteFormat.next_of_ne F (by simp [ne_of_gt hb])]
private theorem exists_step_rep_le {F : FiniteFormat} {g : _root_.Mpfx.Dyadic}
    (hg_p : _root_.Mpfx.Dyadic.precisionAtMost F.p g) (hg_q : _root_.Mpfx.Dyadic.quantumAtLeast F.exp g) {s : ℤ}
    (hs : s ≤ F.canonicalExp ((g : _root_.Mpfx.Dyadic) : ℝ)) :
    ∃ m : ℤ, ((g : _root_.Mpfx.Dyadic) : ℝ) = (m : ℝ) * (2 : ℝ) ^ s := by
  set t := F.canonicalExp ((g : _root_.Mpfx.Dyadic) : ℝ) with ht
  obtain ⟨m, hm⟩ := F.exists_mul_zpow_canonicalExp ⟨hg_p, hg_q, trivial⟩
  exact ⟨m * 2 ^ ((t - s).toNat), by
    rw [hm, two_zpow_split_toNat hs]; push_cast; ring⟩
end Mpfx
end

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F : FiniteFormat} {b g : _root_.Mpfx.Dyadic}
    (hb_mem : b ∈ F.unbounded) (hg_mem : g ∈ F.unbounded)
    (hb_nn : 0 ≤ ((b : _root_.Mpfx.Dyadic) : ℝ))
    (hguard : F.exp = ⊥ → 0 < ((b : _root_.Mpfx.Dyadic) : ℝ))
    (hbg : ((b : _root_.Mpfx.Dyadic) : ℝ) < ((g : _root_.Mpfx.Dyadic) : ℝ)) :
    ((F.toFormat.next b : _root_.Mpfx.Dyadic) : ℝ) ≤ ((g : _root_.Mpfx.Dyadic) : ℝ) := by
  obtain ⟨hb_p, hb_q, -⟩ := hb_mem
  obtain ⟨hg_p, hg_q, -⟩ := hg_mem
  have hg_pos : 0 < ((g : _root_.Mpfx.Dyadic) : ℝ) := lt_of_le_of_lt hb_nn hbg
  rcases eq_or_lt_of_le hb_nn with hb0 | hb0
  · -- `b = 0`: the step is the quantum `2 ^ e`, and `g` is a positive multiple of it
    have hbz : b = 0 :=
      eq_zero_of_coe_real_zero hb0.symm
    cases he : F.exp using QExp.recBotCoe with
    | bot => exact absurd (hguard he) (by rw [← hb0]; exact lt_irrefl 0)
    | coe e =>
      have h_next : F.toFormat.next b = _root_.Mpfx.Dyadic.ofIntZpow 1 e := by
        rw [hbz]; exact Format.next_zero _ he
      obtain ⟨m, hm⟩ := (_root_.Mpfx.Dyadic.quantumAtLeast_coe_real e g).mp (he ▸ hg_q)
      have h2e : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
      have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
        have : (0 : ℤ) < m := by
          by_contra hc
          push Not at hc
          have : (m : ℝ) ≤ 0 := by exact_mod_cast hc
          nlinarith [hm ▸ hg_pos]
        exact_mod_cast this
      rw [h_next, coe_real_ofIntZpow_one e, hm]
      nlinarith
  · -- `b > 0`: both are multiples of the step `2 ^ cexp b`
    have h_next := next_pos_eq F hb0
    have hmono : F.canonicalExp ((b : _root_.Mpfx.Dyadic) : ℝ) ≤ F.canonicalExp ((g : _root_.Mpfx.Dyadic) : ℝ) :=
      FiniteFormat.canonicalExp_mono F (ne_of_gt hb0)
        (by rw [abs_of_pos hb0, abs_of_pos hg_pos]; linarith)
    obtain ⟨mb, hmb⟩ := exists_step_rep_le (F := F) hb_p hb_q le_rfl
    obtain ⟨mg, hmg⟩ := exists_step_rep_le (F := F) hg_p hg_q hmono
    exact next_ulp_min hmb hmg hbg h_next
end Mpfx
