-- Prove2me | solution 1 for P2M_Mpfx_next_mem_unbounded__2b8c4e4daa3e
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:53:00.631052+00:00
-- url     : https://prove2.me/submissions/0c390a57-a137-4f5c-95ee-48ff384e10b1

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
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_coe
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_coe_real
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_neg_iff
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_top
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_bot
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_coe_real
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_neg_iff
import Theorems.Thm_Mpfx_FiniteFormat_exists_mul_zpow_canonicalExp
import Theorems.Thm_Mpfx_FiniteFormat_exp_le_canonicalExp
import Theorems.Thm_Mpfx_FiniteFormat_extend_toFormat
import Theorems.Thm_Mpfx_FiniteFormat_log_sub_p_le_canonicalExp
import Theorems.Thm_Mpfx_FiniteFormat_p_pos
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
import Theorems.Thm_Mpfx_abs_one_lt_two_pow
import Theorems.Thm_Mpfx_coe_real_ofIntZpow_one
import Theorems.Thm_Mpfx_eq_zero_of_coe_real_zero
import Theorems.Thm_Mpfx_exists_p_coe_of_exp_bot
import Theorems.Thm_Mpfx_precisionAtMost_one_zpow
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
private theorem next_ulp_precision {F : Format} {p : ℕ} (hp : 0 < p) {b : _root_.Mpfx.Dyadic}
    (hb0 : 0 < ((b : _root_.Mpfx.Dyadic) : ℝ)) {m s : ℤ}
    (hm : ((b : _root_.Mpfx.Dyadic) : ℝ) = (m : ℝ) * (2 : ℝ) ^ s)
    (hs : Int.log 2 ((b : _root_.Mpfx.Dyadic) : ℝ) - (p : ℤ) + 1 ≤ s)
    (h_next : F.next b = b + _root_.Mpfx.Dyadic.ofIntZpow 1 s) :
    _root_.Mpfx.Dyadic.precisionAtMost (p : Prec) (F.next b) ∧
    ((F.next b : _root_.Mpfx.Dyadic) : ℝ) = ((m + 1 : ℤ) : ℝ) * (2 : ℝ) ^ s := by
  have h2s_pos : (0 : ℝ) < (2 : ℝ) ^ s := zpow_pos (by norm_num) _
  have h_val : ((F.next b : _root_.Mpfx.Dyadic) : ℝ) = ((m + 1 : ℤ) : ℝ) * (2 : ℝ) ^ s := by
    rw [h_next, _root_.Mpfx.Dyadic.coe_real_add, coe_real_ofIntZpow_one s, hm]
    push_cast; ring
  have hm_pos : 0 < m := by
    rcases le_or_gt m 0 with hneg | hpos
    · exfalso
      have h0 : (m : ℝ) ≤ 0 := by exact_mod_cast hneg
      nlinarith
    · exact hpos
  -- `m < 2^p`: one binade above `b` clears the precision budget.
  have hm_lt : m < 2 ^ p := by
    have hb_ub : ((b : _root_.Mpfx.Dyadic) : ℝ)
        < (2 : ℝ) ^ (Int.log 2 ((b : _root_.Mpfx.Dyadic) : ℝ) + 1) :=
      Int.lt_zpow_succ_log_self (by norm_num) _
    have h3 : (m : ℝ) * (2 : ℝ) ^ s < (2 : ℝ) ^ (p : ℤ) * (2 : ℝ) ^ s := by
      have h5 : (2 : ℝ) ^ ((p : ℤ) + s)
          = (2 : ℝ) ^ (p : ℤ) * (2 : ℝ) ^ s := by
        rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      rw [← h5]
      calc (m : ℝ) * (2 : ℝ) ^ s = ((b : _root_.Mpfx.Dyadic) : ℝ) := hm.symm
        _ < (2 : ℝ) ^ (Int.log 2 ((b : _root_.Mpfx.Dyadic) : ℝ) + 1) := hb_ub
        _ ≤ (2 : ℝ) ^ ((p : ℤ) + s) :=
            zpow_le_zpow_right₀ (by norm_num) (by omega)
    have h6 : (m : ℝ) < (2 : ℝ) ^ (p : ℤ) :=
      lt_of_mul_lt_mul_right h3 h2s_pos.le
    have h7 : (m : ℝ) < (2 : ℝ) ^ p := by
      rw [← zpow_natCast (2 : ℝ) p]; exact h6
    exact_mod_cast h7
  rcases lt_or_eq_of_le (Int.add_one_le_iff.mpr hm_lt) with h_lt | h_eq
  · -- Normal case: representation `(m + 1, s)`.
    refine ⟨?_, h_val⟩
    rw [_root_.Mpfx.Dyadic.precisionAtMost_coe_real]
    exact ⟨m + 1, s, h_val, by rwa [abs_of_pos (by omega : (0 : ℤ) < m + 1)]⟩
  · -- Carry case: `next b = 2^(p + s)`, representation `(1, p + s)`.
    have h_val' : ((F.next b : _root_.Mpfx.Dyadic) : ℝ) = (2 : ℝ) ^ ((p : ℤ) + s) := by
      rw [h_val, h_eq, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast]
      push_cast; ring
    refine ⟨?_, h_val⟩
    rw [_root_.Mpfx.Dyadic.precisionAtMost_coe_real]
    exact ⟨1, (p : ℤ) + s, by rw [h_val']; push_cast; ring,
      abs_one_lt_two_pow hp⟩
private theorem next_pos_eq (F : FiniteFormat) {b : _root_.Mpfx.Dyadic} (hb : 0 < ((b : _root_.Mpfx.Dyadic) : ℝ)) :
    F.toFormat.next b = b + _root_.Mpfx.Dyadic.ofIntZpow 1 (F.canonicalExp ((b : _root_.Mpfx.Dyadic) : ℝ)) := by
  rw [FiniteFormat.next_eq_format_next F hb,
    FiniteFormat.next_of_ne F (by simp [ne_of_gt hb])]
end Mpfx
end

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F : FiniteFormat} {b : _root_.Mpfx.Dyadic}
    (hb_mem : b ∈ F.unbounded) (hb_nn : 0 ≤ ((b : _root_.Mpfx.Dyadic) : ℝ)) :
    F.toFormat.next b ∈ F.unbounded := by
  obtain ⟨hb_p, hb_q, -⟩ := hb_mem
  rcases eq_or_lt_of_le hb_nn with hb0 | hb0
  · -- `b = 0`: the step is the format's own quantum, or `1` when it has none
    have hbz : b = 0 :=
      eq_zero_of_coe_real_zero hb0.symm
    cases he : F.exp using QExp.recBotCoe with
    | bot =>
      obtain ⟨p, hF_p⟩ := exists_p_coe_of_exp_bot he
      rw [Format.next_eq_bot_nonpos F.toFormat he (le_of_eq hb0.symm), hbz, zero_add]
      refine ⟨?_, by change _root_.Mpfx.Dyadic.quantumAtLeast F.exp _; rw [he]; trivial, trivial⟩
      change _root_.Mpfx.Dyadic.precisionAtMost F.p (1 : _root_.Mpfx.Dyadic)
      rw [hF_p, _root_.Mpfx.Dyadic.precisionAtMost_coe]
      exact ⟨1, 0, by push_cast; norm_num, abs_one_lt_two_pow (F.p_pos hF_p)⟩
    | coe e =>
      have h_next : F.toFormat.next b = _root_.Mpfx.Dyadic.ofIntZpow 1 e := by
        rw [hbz]; exact Format.next_zero _ he
      rw [h_next]
      refine ⟨?_, ?_, trivial⟩
      · change _root_.Mpfx.Dyadic.precisionAtMost F.p _
        cases hp : F.p using ENat.recTopCoe with
        | top => trivial
        | coe p => exact precisionAtMost_one_zpow (fun hz => (F.p_pos hp).ne' (ENat.coe_inj.mp hz)) e
      · change _root_.Mpfx.Dyadic.quantumAtLeast F.exp _
        rw [he, _root_.Mpfx.Dyadic.quantumAtLeast_coe_real]
        exact ⟨1, by rw [_root_.Mpfx.Dyadic.coe_ofIntZpow]⟩
  · -- `b > 0`: one step of `2 ^ cexp b`, which both clauses can absorb
    have hbne : ((b : _root_.Mpfx.Dyadic) : ℝ) ≠ 0 := ne_of_gt hb0
    have h_next := next_pos_eq F hb0
    refine ⟨?_, ?_, trivial⟩
    · change _root_.Mpfx.Dyadic.precisionAtMost F.p _
      cases hp : F.p using ENat.recTopCoe with
      | top => trivial
      | coe p =>
        obtain ⟨m, hm⟩ := F.exists_mul_zpow_canonicalExp ⟨hb_p, hb_q, trivial⟩
        exact (next_ulp_precision (F := F.toFormat) (p := p) (F.p_pos hp) hb0 hm
          (by have := F.log_sub_p_le_canonicalExp hbne hp
              rw [abs_of_pos hb0] at this; omega) h_next).1
    · change _root_.Mpfx.Dyadic.quantumAtLeast F.exp _
      cases he : F.exp using QExp.recBotCoe with
      | bot => trivial
      | coe e =>
        rw [_root_.Mpfx.Dyadic.quantumAtLeast_coe_real]
        obtain ⟨m, hm⟩ := (_root_.Mpfx.Dyadic.quantumAtLeast_coe_real e b).mp (he ▸ hb_q)
        refine ⟨m + 2 ^ ((F.canonicalExp ((b : _root_.Mpfx.Dyadic) : ℝ) - e).toNat), ?_⟩
        rw [h_next, _root_.Mpfx.Dyadic.coe_real_add, coe_real_ofIntZpow_one, hm,
          two_zpow_split_toNat (F.exp_le_canonicalExp _ he)]
        push_cast; ring
end Mpfx
