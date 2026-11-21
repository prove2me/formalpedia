-- Prove2me | solution 1 for Mpfx.FiniteFormat.exists_mul_zpow_canonicalExp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:52:00.860749+00:00
-- url     : https://prove2.me/submissions/c9bd3a17-3d53-4fe3-b545-d9582c8b04b5

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
import Theorems.Thm_Mpfx_Special_neg_neg
import Theorems.Thm_Mpfx_WithSpecial_neg_finite
import Theorems.Thm_Mpfx_WithSpecial_neg_special
import Theorems.Thm_Mpfx_WithSpecial_neg_neg
import Theorems.Thm_Mpfx_WithSpecial_toReal_finite
import Theorems.Thm_Mpfx_WithSpecial_toReal_special
import Theorems.Thm_Mpfx_Format_unbounded_p
import Theorems.Thm_Mpfx_Format_unbounded_exp
import Theorems.Thm_Mpfx_Format_unbounded_b
import Theorems.Thm_Mpfx_Format_unbounded_specials
import Theorems.Thm_Mpfx_Format_unbounded_unbounded
import Theorems.Thm_Mpfx_Format_finite_mem_values
import Theorems.Thm_Mpfx_Format_special_mem_values
import Theorems.Thm_Mpfx_Format_boundOK_zero
import Theorems.Thm_Mpfx_Format_boundOK_neg_iff
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_toFormat
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_p
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_canonicalExp
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_exp
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_b
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_unbounded
import Theorems.Thm_Mpfx_canonicalExp_expBot
import Theorems.Thm_Mpfx_canonicalExp_expFinite
import Theorems.Thm_Mpfx_canonicalExp_pTop
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
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_coe_real
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_neg_iff
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_top
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_bot
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_coe_real
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_neg_iff
import Theorems.Thm_Mpfx_abs_mul_two_zpow
import Theorems.Thm_Mpfx_two_zpow_shift
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


attribute [local simp] Mpfx.Special.neg_neg
attribute [local simp] Mpfx.WithSpecial.neg_finite
attribute [local simp] Mpfx.WithSpecial.neg_special
attribute [local simp] Mpfx.WithSpecial.neg_neg
attribute [local simp] Mpfx.WithSpecial.toReal_finite
attribute [local simp] Mpfx.WithSpecial.toReal_special
attribute [local simp] Mpfx.Format.unbounded_p
attribute [local simp] Mpfx.Format.unbounded_exp
attribute [local simp] Mpfx.Format.unbounded_b
attribute [local simp] Mpfx.Format.unbounded_specials
attribute [local simp] Mpfx.Format.unbounded_unbounded
attribute [local simp] Mpfx.Format.finite_mem_values
attribute [local simp] Mpfx.Format.special_mem_values
attribute [local simp] Mpfx.Format.boundOK_zero
attribute [local simp] Mpfx.Format.boundOK_neg_iff
attribute [local simp] Mpfx.FiniteFormat.unbounded_toFormat
attribute [local simp] Mpfx.FiniteFormat.unbounded_p
attribute [local simp] Mpfx.FiniteFormat.unbounded_canonicalExp
attribute [local simp] Mpfx.FiniteFormat.unbounded_exp
attribute [local simp] Mpfx.FiniteFormat.unbounded_b
attribute [local simp] Mpfx.FiniteFormat.unbounded_unbounded

set_option autoImplicit true
open Mpfx
namespace Mpfx
namespace FiniteFormat
theorem _root_.solution (F : FiniteFormat) {z : Dyadic}
    (hz : z ∈ F.unbounded) : ∃ m : ℤ, (z : ℝ) = m * (2 : ℝ) ^ F.canonicalExp z := by
  by_cases hz0 : (z : ℝ) = 0
  · exact ⟨0, by simp [hz0]⟩
  have hquant : ∀ e : ℤ, F.exp = e → ∃ m : ℤ, (z : ℝ) = m * (2 : ℝ) ^ e := fun e he =>
    (Dyadic.quantumAtLeast_coe_real e z).mp (he ▸ hz.2.1)
  have hprec : ∀ p : ℕ, F.p = p →
      ∃ m : ℤ, (z : ℝ) = m * (2 : ℝ) ^ (Int.log 2 |(z : ℝ)| + 1 - p) := fun p hp => by
    obtain ⟨c, e, hce, hc⟩ := (Dyadic.precisionAtMost_coe_real p z).mp (hp ▸ hz.1)
    -- `2^⌊log₂|z|⌋ ≤ |z| = |c|·2^e < 2^(p+e)`, so the precision term is at most `e`.
    have hlo : (2 : ℝ) ^ Int.log 2 |(z : ℝ)| ≤ |(z : ℝ)| := by
      have := Int.zpow_log_le_self (b := 2) (by norm_num) (abs_pos.mpr hz0)
      exact_mod_cast this
    have hhi : |(z : ℝ)| < (2 : ℝ) ^ ((p : ℤ) + e) := by
      rw [hce, abs_mul_two_zpow, zpow_add₀ two_ne_zero, zpow_natCast]
      exact mul_lt_mul_of_pos_right (by exact_mod_cast hc) (zpow_pos two_pos e)
    have hle : Int.log 2 |(z : ℝ)| + 1 - p ≤ e := by
      have := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp (hlo.trans_lt hhi)
      omega
    exact ⟨_, hce.trans (two_zpow_shift c hle)⟩
  cases hp : F.p using ENat.recTopCoe with
  | top =>
    cases he : F.exp using QExp.recBotCoe with
    | bot => exact (F.finite.elim (· hp) (· he)).elim
    | coe e => rw [canonicalExp_pTop hp he]; exact hquant e he
  | coe p =>
    cases he : F.exp using QExp.recBotCoe with
    | bot => rw [canonicalExp_expBot hp he hz0]; exact hprec p hp
    | coe e =>
      rw [canonicalExp_expFinite hp he hz0]
      rcases le_total (Int.log 2 |(z : ℝ)| + 1 - p) e with h | h
      · rw [max_eq_right h]; exact hquant e he
      · rw [max_eq_left h]; exact hprec p hp
end FiniteFormat
end Mpfx
