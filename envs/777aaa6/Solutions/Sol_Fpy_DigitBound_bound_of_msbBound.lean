-- Prove2me | solution 1 for Fpy.DigitBound.bound_of_msbBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:48:35.814721+00:00
-- url     : https://prove2.me/submissions/7ff98d05-5b52-48da-8890-f955c8202e4c

import Definitions.Def_Fpy_DigitBound_Digits
import Definitions.Def_Fpy_FormatInference_Sound
import Definitions.Def_Fpy_DigitBound_Sound
import Theorems.Thm_Fpy_DigitBound_le_of_width
import Theorems.Thm_Fpy_DigitBound_queried
import Theorems.Thm_Fpy_DigitBound_abs_lt_of_msbBound
import Theorems.Thm_Fpy_DigitBound_abs_le_of_grid
import Theorems.Thm_Fpy_DigitBound_EInt_top_add_coe
import Theorems.Thm_Fpy_DigitBound_NumIn_eq
import Theorems.Thm_Fpy_DigitBound_coe_add_coe
import Theorems.Thm_Fpy_DigitBound_coe_le_lsbOf
import Theorems.Thm_Fpy_DigitBound_lsbOf_abs
import Theorems.Thm_Fpy_DigitBound_lsbOf_ne_top
import Theorems.Thm_Fpy_DigitBound_lsbOf_neg
import Theorems.Thm_Fpy_DigitBound_msbOf_abs
import Theorems.Thm_Fpy_DigitBound_msbOf_le_coe
import Theorems.Thm_Fpy_DigitBound_msbOf_neg
import Theorems.Thm_Fpy_DigitBound_numOfE_bot
import Theorems.Thm_Fpy_DigitBound_numOfE_coe
import Theorems.Thm_Fpy_DigitBound_numOfE_top
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
import Theorems.Thm_Mpfx_FiniteFormat_IsEven_neg_iff
import Theorems.Thm_Mpfx_FiniteFormat_IsOdd_neg_iff
import Theorems.Thm_Mpfx_FiniteFormat_extend_toFormat
import Theorems.Thm_Mpfx_FiniteFormat_isEven_zero
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_b
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_canonicalExp
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_exp
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_isUndefined
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
import Theorems.Thm_Mpfx_rnd_special
attribute [local simp] Fpy.DigitBound.EInt.top_add_coe
attribute [local simp] Fpy.DigitBound.lsbOf_abs
attribute [local simp] Fpy.DigitBound.lsbOf_neg
attribute [local simp] Fpy.DigitBound.msbOf_abs
attribute [local simp] Fpy.DigitBound.msbOf_neg
attribute [local simp] Fpy.DigitBound.numOfE_bot
attribute [local simp] Fpy.DigitBound.numOfE_coe
attribute [local simp] Fpy.DigitBound.numOfE_top
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
attribute [local simp] Mpfx.FiniteFormat.IsEven.neg_iff
attribute [local simp] Mpfx.FiniteFormat.IsOdd.neg_iff
attribute [local simp] Mpfx.FiniteFormat.extend_toFormat
attribute [local simp] Mpfx.FiniteFormat.isEven_zero
attribute [local simp] Mpfx.FiniteFormat.unbounded_b
attribute [local simp] Mpfx.FiniteFormat.unbounded_canonicalExp
attribute [local simp] Mpfx.FiniteFormat.unbounded_exp
attribute [local simp] Mpfx.FiniteFormat.unbounded_isUndefined
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
attribute [local simp] Mpfx.rnd_special



set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx} {Φ : Program (fpy decode)}
  {D : FormatDomain} {A : Analysis (fpy decode) D}
local notation "nan" => (WithSpecial.special Special.nan : Num)
variable {Ψ : List Con} {ι : Asgn} {l m : Term} {τ : Option Term} {x : ℝ}
namespace Fpy.DigitBound
theorem _root_.solution {k lo : ℤ} (hs : Sat ι Ψ)
    (hd : Describes Ψ ι (.num l m τ) (.num (.finite x))) (hk : msbBound Ψ m ≤ k)
    (hlo : lo ≤ k)
    (h : (lo : EInt) ≤ lsbBound Ψ l m ∨ precBound Ψ l m ≤ ((k - lo + 1 : ℤ) : EInt)) :
    |x| ≤ 2 ^ (k + 1) - 2 ^ lo := by
  have hx := abs_lt_of_msbBound hs hd hk
  have hlok : (2 : ℝ) ^ lo ≤ 2 ^ k := zpow_le_zpow_right₀ (by norm_num) hlo
  have h2 : (2 : ℝ) ^ (k + 1) = 2 ^ k * 2 := zpow_add_one₀ two_ne_zero k
  have hk0 : (0 : ℝ) < 2 ^ k := zpow_pos two_pos k
  by_cases h0 : x = 0
  · rw [h0, abs_zero]; linarith
  have hq := queried hs hd h0
  by_cases hg : (lo : EInt) ≤ lsbOf (.finite x)
  · obtain ⟨c, rfl⟩ := coe_le_lsbOf.mp hg
    exact abs_le_of_grid hx hlo
  obtain ⟨hl, hm⟩ : lsbOf _ = l.eval ι ∧ msbOf _ = m.eval ι := by
    cases hd with | num hu => exact hu.eq (by simp)
  rcases h with h | h
  · exact absurd (h.trans (hl ▸ iInf₂_le (f := fun ι (_ : Queried Ψ m ι) => l.eval ι) ι hq)) hg
  have hw := le_of_width
    ((le_iSup₂ (f := fun ι (_ : Queried Ψ m ι) => (l.width m).eval ι) ι hq).trans h)
  rw [← hl, ← hm] at hw
  have hmk : msbOf (.finite x) ≤ ((k - 1 : ℤ) : EInt) := by
    refine hw.trans ?_
    cases ha : lsbOf (.finite x) using WithBotTop.rec with
    | bot => exact bot_le.trans' (le_of_eq (by simp))
    | top => exact absurd ha (lsbOf_ne_top h0)
    | coe a =>
      rw [ha, WithBotTop.coe_le_coe, not_le] at hg
      rw [coe_add_coe, WithBotTop.coe_le_coe]
      omega
  have := msbOf_le_coe.mp hmk
  rw [sub_add_cancel] at this
  linarith
end Fpy.DigitBound
