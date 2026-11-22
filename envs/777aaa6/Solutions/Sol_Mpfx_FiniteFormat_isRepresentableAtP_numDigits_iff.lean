-- Prove2me | solution 1 for Mpfx.FiniteFormat.isRepresentableAtP_numDigits_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:09:40.848812+00:00
-- url     : https://prove2.me/submissions/b2234279-06a7-41a8-b409-298a84580fc5

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Format_Parity
import Theorems.Thm_Mpfx_FiniteFormat_IsOdd_neg_iff
import Theorems.Thm_Mpfx_FiniteFormat_isEven_zero
import Theorems.Thm_Mpfx_FiniteFormat_IsEven_neg_iff
import Theorems.Thm_Mpfx_Dyadic_coe_abs
import Theorems.Thm_Mpfx_Dyadic_coe_half
import Theorems.Thm_Mpfx_Dyadic_coe_ofIntZpow
import Theorems.Thm_Mpfx_Dyadic_coe_rat_abs
import Theorems.Thm_Mpfx_Dyadic_coe_rat_half
import Theorems.Thm_Mpfx_Dyadic_coe_rat_ofIntZpow
import Theorems.Thm_Mpfx_Dyadic_coe_real_add
import Theorems.Thm_Mpfx_Dyadic_coe_real_eq_ratCast
import Theorems.Thm_Mpfx_Dyadic_coe_real_inj
import Theorems.Thm_Mpfx_Dyadic_coe_real_mul
import Theorems.Thm_Mpfx_Dyadic_coe_real_neg
import Theorems.Thm_Mpfx_Dyadic_coe_real_sub
import Theorems.Thm_Mpfx_Dyadic_coe_real_zero
import Theorems.Thm_Mpfx_Dyadic_isRepresentableAtP_of_log
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_neg_iff
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_top
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_bot
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_neg_iff
import Theorems.Thm_Mpfx_FiniteFormat_extend_toFormat
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_b
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_canonicalExp
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_exp
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_p
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_toFormat
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_unbounded
import Theorems.Thm_Mpfx_Format_boundAfterNext_top
import Theorems.Thm_Mpfx_Format_boundOK_neg_iff
import Theorems.Thm_Mpfx_Format_boundOK_zero
import Theorems.Thm_Mpfx_Format_finite_mem_values
import Theorems.Thm_Mpfx_Format_special_mem_values
import Theorems.Thm_Mpfx_Format_unbounded_b
import Theorems.Thm_Mpfx_Format_unbounded_exp
import Theorems.Thm_Mpfx_Format_unbounded_p
import Theorems.Thm_Mpfx_Format_unbounded_specials
import Theorems.Thm_Mpfx_Format_unbounded_unbounded
import Theorems.Thm_Mpfx_Format_withBound_b
import Theorems.Thm_Mpfx_Format_withBound_exp
import Theorems.Thm_Mpfx_Format_withBound_p
import Theorems.Thm_Mpfx_Format_withBound_specials
import Theorems.Thm_Mpfx_Special_neg_neg
import Theorems.Thm_Mpfx_WithSpecial_neg_finite
import Theorems.Thm_Mpfx_WithSpecial_neg_neg
import Theorems.Thm_Mpfx_WithSpecial_neg_special
import Theorems.Thm_Mpfx_WithSpecial_toReal_finite
import Theorems.Thm_Mpfx_WithSpecial_toReal_special
import Theorems.Thm_Mpfx_abs_mul_two_zpow
import Theorems.Thm_Mpfx_log_abs_mul_zpow
import Theorems.Thm_Mpfx_log_eq_of_zpow_bounds
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
attribute [local simp] Mpfx.Format.boundAfterNext_top
attribute [local simp] Mpfx.Format.boundOK_neg_iff
attribute [local simp] Mpfx.Format.boundOK_zero
attribute [local simp] Mpfx.Format.finite_mem_values
attribute [local simp] Mpfx.Format.special_mem_values
attribute [local simp] Mpfx.Format.unbounded_b
attribute [local simp] Mpfx.Format.unbounded_exp
attribute [local simp] Mpfx.Format.unbounded_p
attribute [local simp] Mpfx.Format.unbounded_specials
attribute [local simp] Mpfx.Format.unbounded_unbounded
attribute [local simp] Mpfx.Format.withBound_b
attribute [local simp] Mpfx.Format.withBound_exp
attribute [local simp] Mpfx.Format.withBound_p
attribute [local simp] Mpfx.Format.withBound_specials
attribute [local simp] Mpfx.Special.neg_neg
attribute [local simp] Mpfx.WithSpecial.neg_finite
attribute [local simp] Mpfx.WithSpecial.neg_neg
attribute [local simp] Mpfx.WithSpecial.neg_special
attribute [local simp] Mpfx.WithSpecial.toReal_finite
attribute [local simp] Mpfx.WithSpecial.toReal_special


attribute [local simp] Mpfx.FiniteFormat.IsOdd.neg_iff
attribute [local simp] Mpfx.FiniteFormat.isEven_zero
attribute [local simp] Mpfx.FiniteFormat.IsEven.neg_iff

set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat
namespace Mpfx.FiniteFormat
theorem _root_.solution (F : FiniteFormat) {y : Dyadic} {c e : ℤ} :
    Dyadic.IsRepresentableAtP (F.numDigits (y : ℝ)).toNat c e y ↔
      (y : ℝ) ≠ 0 ∧ e = F.canonicalExp y ∧ (y : ℝ) = c * 2 ^ e := by
  constructor
  · rintro ⟨hyq, hlo, hhi⟩
    have hy : (y : ℝ) = c * 2 ^ e := by
      rw [Dyadic.coe_real_eq_ratCast, hyq]; push_cast; ring
    set n := (F.numDigits (y : ℝ)).toNat with hn
    have hn1 : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · have h1 : |c| < 1 := by simpa [h0] using hhi
        have h2 : 1 ≤ |c| := by simpa [h0] using hlo
        omega
      · exact h0
    have hc0 : c ≠ 0 := by
      rintro rfl
      have := pow_pos (two_pos : (0 : ℤ) < 2) (n - 1)
      simp at hlo; omega
    have hy0 : (y : ℝ) ≠ 0 := by
      rw [hy]; exact mul_ne_zero (by exact_mod_cast hc0) (zpow_pos two_pos e).ne'
    -- `2^(n-1) ≤ |c| < 2^n` puts `|y| = |c| · 2^e` in binade `n - 1 + e`.
    have hlog : Int.log 2 |(y : ℝ)| = (n - 1 : ℕ) + e := by
      have hlo' : (2 : ℝ) ^ ((n - 1 : ℕ) : ℤ) ≤ |(c : ℝ)| := by
        rw [zpow_natCast]; exact_mod_cast hlo
      have hhi' : |(c : ℝ)| < (2 : ℝ) ^ (((n - 1 : ℕ) : ℤ) + 1) := by
        rw [show ((n - 1 : ℕ) : ℤ) + 1 = (n : ℤ) by omega, zpow_natCast]; exact_mod_cast hhi
      have h2e : (0 : ℝ) < 2 ^ e := zpow_pos two_pos e
      rw [hy, abs_mul_two_zpow]
      refine log_eq_of_zpow_bounds (mul_pos (abs_pos.mpr (by exact_mod_cast hc0)) h2e) ?_ ?_
      · rw [zpow_add₀ two_ne_zero]; exact mul_le_mul_of_nonneg_right hlo' h2e.le
      · rw [show ((n - 1 : ℕ) : ℤ) + e + 1 = (((n - 1 : ℕ) : ℤ) + 1) + e by ring,
          zpow_add₀ two_ne_zero]
        exact mul_lt_mul_of_pos_right hhi' h2e
    have hnd : (n : ℤ) = F.numDigits (y : ℝ) := Int.toNat_of_nonneg (by omega)
    rw [numDigits, if_neg hy0] at hnd
    exact ⟨hy0, by omega, hy⟩
  · rintro ⟨hy0, rfl, hy⟩
    set e := F.canonicalExp (y : ℝ)
    have hc0 : c ≠ 0 := by rintro rfl; exact hy0 (by rw [hy]; simp)
    have hL : 0 ≤ Int.log 2 |(c : ℝ)| := by
      rw [Int.log_of_one_le_right _ (by exact_mod_cast Int.one_le_abs hc0)]
      exact Nat.cast_nonneg _
    have hlog : Int.log 2 |(y : ℝ)| = Int.log 2 |(c : ℝ)| + e := by
      rw [hy, log_abs_mul_zpow hc0]
    have hnd : (F.numDigits (y : ℝ)).toNat = (Int.log 2 |(c : ℝ)|).toNat + 1 := by
      rw [numDigits, if_neg hy0, hlog]; omega
    rw [hnd]
    refine Dyadic.isRepresentableAtP_of_log hc0 ?_
    have : ((y : ℚ) : ℝ) = ((c * 2 ^ e : ℚ) : ℝ) := by
      rw [← Dyadic.coe_real_eq_ratCast, hy]; push_cast; ring
    exact_mod_cast this
end Mpfx.FiniteFormat
