-- Prove2me | solution 1 for Mpfx.FiniteFormat.exp_eq_canonicalExp_of_p_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:22:49.020716+00:00
-- url     : https://prove2.me/submissions/d2365f28-d3d9-480c-b511-708b5c93d5a9

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Format_Parity
import Theorems.Thm_Mpfx_FiniteFormat_IsOdd_neg_iff
import Theorems.Thm_Mpfx_FiniteFormat_IsOdd_ne_zero
import Theorems.Thm_Mpfx_FiniteFormat_isEven_zero
import Theorems.Thm_Mpfx_FiniteFormat_IsEven_neg_iff
import Theorems.Thm_Mpfx_FiniteFormat_not_isEven_and_isOdd
import Theorems.Thm_Mpfx_FiniteFormat_isEven_iff_mem_shrink
import Theorems.Thm_Mpfx_FiniteFormat_p_ne_one_of_two_le
import Theorems.Thm_Mpfx_Dyadic_IsRepresentableAtP_ne_zero
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
import Theorems.Thm_Mpfx_Dyadic_ext_real
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_neg_iff
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_top
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_bot
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_neg_iff
import Theorems.Thm_Mpfx_FiniteFormat_exists_mul_zpow_canonicalExp
import Theorems.Thm_Mpfx_FiniteFormat_extend_toFormat
import Theorems.Thm_Mpfx_FiniteFormat_shrink_exp_bot
import Theorems.Thm_Mpfx_FiniteFormat_shrink_exp_coe
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_b
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_canonicalExp
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_exp
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_p
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_toFormat
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_unbounded
import Theorems.Thm_Mpfx_Format_boundAfterNext_top
import Theorems.Thm_Mpfx_Format_boundOK_neg_iff
import Theorems.Thm_Mpfx_Format_boundOK_zero
import Theorems.Thm_Mpfx_Format_exp_le_of_subset
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
import Theorems.Thm_Mpfx_eq_zero_of_coe_real_zero
import Theorems.Thm_Mpfx_exp_le_canonicalExp_coe
import Theorems.Thm_Mpfx_floor_mantissa_lt
import Theorems.Thm_Mpfx_mem_unbounded_of_mem
import Theorems.Thm_Mpfx_ofIntZpow_mem_unbounded
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
theorem _root_.solution {F₁ : FiniteFormat} {F₂ : FiniteFormat}
    (hsub : F₁.toFormat ⊆ F₂.toFormat) (hp : ((2 : ℕ) : Prec) ≤ F₂.p)
    (hp₁ : F₁.p = ((1 : ℕ) : Prec)) {y : Dyadic} (hy : y ∈ F₁) (hodd : F₂.IsOdd y) :
    F₁.exp = ((F₁.canonicalExp y : ℤ) : QExp) := by
  have hy0 : (y : ℝ) ≠ 0 := fun h => hodd.ne_zero (eq_zero_of_coe_real_zero h)
  obtain ⟨c, hc⟩ := F₁.exists_mul_zpow_canonicalExp (mem_unbounded_of_mem hy)
  set j := F₁.canonicalExp y
  -- The significand of a precision-`1` value is `±1`.
  have hc1 : |c| = 1 := by
    have h := floor_mantissa_lt (F := F₁) (x := y) hp₁
    change |(y : ℝ) * 2 ^ (-j)| < 2 ^ 1 at h
    rw [hc, mul_assoc, ← zpow_add₀ two_ne_zero, add_neg_cancel, zpow_zero, mul_one] at h
    have : |c| < 2 := by exact_mod_cast (show |(c : ℝ)| < 2 by simpa using h)
    have : c ≠ 0 := by rintro rfl; exact hy0 (by rw [hc]; simp)
    have := Int.one_le_abs this
    omega
  have hyc : y = Dyadic.ofIntZpow c j := Dyadic.ext_real (by rw [Dyadic.coe_ofIntZpow]; exact hc)
  have h₂₁ := Format.exp_le_of_subset ⟨y, hy, hodd.ne_zero⟩ hsub
  have h₁j := exp_le_canonicalExp_coe F₁ (y : ℝ)
  by_contra hne
  -- Otherwise `y = ±2^j` with `j` above `F₂`'s quantum lies in `F₂`'s shrink.
  have hC : y ∈ (F₂.shrink (p_ne_one_of_two_le hp)).unbounded := by
    rw [hyc]
    refine ofIntZpow_mem_unbounded _ (fun {e'} he' => ?_) (fun {q} hq => ?_)
    · cases he₂ : F₂.exp using QExp.recBotCoe with
      | bot => rw [FiniteFormat.shrink_exp_bot _ he₂] at he'; exact absurd he' WithBot.bot_ne_coe
      | coe e₂ =>
        rw [FiniteFormat.shrink_exp_coe _ he₂, WithBot.coe_inj] at he'
        cases he₁ : F₁.exp using QExp.recBotCoe with
        | bot => rw [he₁, he₂] at h₂₁; exact absurd h₂₁ (by simp)
        | coe e₁ =>
          rw [he₁, he₂, WithBot.coe_le_coe] at h₂₁
          rw [he₁, WithBot.coe_le_coe] at h₁j
          rw [he₁, WithBot.coe_inj] at hne
          omega
    · rw [hc1]; exact one_le_pow₀ (by norm_num)
  exact not_isEven_and_isOdd ((isEven_iff_mem_shrink F₂ _ y).mpr hC) hodd
end Mpfx.FiniteFormat
