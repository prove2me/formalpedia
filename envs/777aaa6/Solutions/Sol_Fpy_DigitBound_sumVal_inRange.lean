-- Prove2me | solution 1 for Fpy.DigitBound.sumVal_inRange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:49:06.982405+00:00
-- url     : https://prove2.me/submissions/5418a791-2c50-494b-bf60-e83f2203d01f

import Definitions.Def_Fpy_DigitBound_Sound
import Definitions.Def_Fpy_Sum
import Definitions.Def_Fpy_DigitBound_Sum
import Theorems.Thm_Fpy_DigitBound_Num_add_nan_left
import Theorems.Thm_Fpy_DigitBound_Num_add_nan_right
import Theorems.Thm_Fpy_DigitBound_sumVal_inv
import Theorems.Thm_Fpy_DigitBound_EInt_top_add_coe
import Theorems.Thm_Fpy_DigitBound_LsbAt_le
import Theorems.Thm_Fpy_DigitBound_coe_add_coe
import Theorems.Thm_Fpy_DigitBound_lsbOf_abs
import Theorems.Thm_Fpy_DigitBound_lsbOf_neg
import Theorems.Thm_Fpy_DigitBound_lsb_add
import Theorems.Thm_Fpy_DigitBound_msbOf_abs
import Theorems.Thm_Fpy_DigitBound_msbOf_le_coe
import Theorems.Thm_Fpy_DigitBound_msbOf_neg
import Theorems.Thm_Fpy_DigitBound_msbOf_of_ne_zero
import Theorems.Thm_Fpy_DigitBound_msbOf_special
import Theorems.Thm_Fpy_DigitBound_msbOf_zero
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


attribute [local simp] Fpy.DigitBound.Num.add_nan_left
attribute [local simp] Fpy.DigitBound.Num.add_nan_right

set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
namespace Fpy.DigitBound
theorem _root_.solution {lo hi : EInt} {us : List Num} (hL : 1 ≤ us.length)
    (hus : ∀ u ∈ us, InRange lo hi u) :
    InRange lo (hi + ((Nat.clog 2 us.length : ℕ) : ℤ)) (sumVal id us) := by
  set c := Nat.clog 2 us.length
  -- The least significant digit never drops below `lo`.
  have hlsb := sumVal_inv (P := fun _ s => s = nan ∨ lo ≤ lsbOf s) (Q := InRange lo hi)
    (fun _ s w hs hw => by
      rcases hs with rfl | hs
      · exact .inl (Num.add_nan_left w)
      rcases hw with rfl | ⟨hw, -⟩
      · exact .inl (Num.add_nan_right s)
      exact .inr ((le_min hs hw).trans (lsb_add s w)))
    (fun u hu => hu.imp id And.left) hL hus
  by_cases hn : sumVal id us = nan
  · exact .inl hn
  refine .inr ⟨hlsb.resolve_left hn, ?_⟩
  cases hi using WithBotTop.rec with
  | top => simp
  | bot =>
    -- Every term is zero.
    have h0 := sumVal_inv (P := fun _ s => s = nan ∨ s = .finite 0) (Q := InRange lo ⊥)
      (fun _ s w hs hw => by
        rcases hs with rfl | rfl
        · exact .inl (Num.add_nan_left w)
        rcases hw with rfl | ⟨-, hw⟩
        · exact .inl rfl
        rcases w with x | _
        · by_cases hx : x = 0
          · exact .inr (by simp [Num.add, hx])
          · exact absurd hw (by simp [msbOf_of_ne_zero hx])
        · exact absurd hw (by simp [msbOf_special]))
      (fun u hu => by
        rcases hu with rfl | ⟨-, hu⟩
        · exact .inl rfl
        rcases u with x | _
        · by_cases hx : x = 0
          · exact .inr (by rw [hx])
          · exact absurd hu (by simp [msbOf_of_ne_zero hx])
        · exact absurd hu (by simp [msbOf_special])) hL hus
    rw [h0.resolve_left hn, msbOf_zero]
    exact bot_le
  | coe h =>
    -- A partial sum of `k` terms has magnitude below `k · 2^(h+1)`.
    have hmag := sumVal_inv
      (P := fun k s => s = nan ∨ ∃ x, s = .finite x ∧ |x| < k * 2 ^ (h + 1))
      (Q := InRange lo h)
      (fun k s w hs hw => by
        rcases hs with rfl | ⟨x, rfl, hx⟩
        · exact .inl (Num.add_nan_left w)
        rcases hw with rfl | ⟨-, hw⟩
        · exact .inl (Num.add_nan_right _)
        rcases w with y | _
        · refine .inr ⟨x + y, rfl, (abs_add_le x y).trans_lt ?_⟩
          have := msbOf_le_coe.mp hw
          push_cast; linarith
        · exact absurd hw (by simp [msbOf_special]))
      (fun u hu => by
        rcases hu with rfl | ⟨-, hu⟩
        · exact .inl rfl
        rcases u with x | _
        · exact .inr ⟨x, rfl, by simpa using msbOf_le_coe.mp hu⟩
        · exact absurd hu (by simp [msbOf_special])) hL hus
    obtain ⟨x, hx, hlt⟩ := hmag.resolve_left hn
    rw [hx, coe_add_coe]
    refine msbOf_le_coe.mpr (hlt.trans_le ?_)
    have hc : (us.length : ℝ) ≤ 2 ^ c := by exact_mod_cast Nat.le_pow_clog (by norm_num) _
    rw [show h + c + 1 = (c : ℤ) + (h + 1) by ring,
      show (2 : ℝ) ^ ((c : ℤ) + (h + 1)) = 2 ^ c * 2 ^ (h + 1) by
        rw [zpow_add₀ two_ne_zero, zpow_natCast]]
    exact mul_le_mul_of_nonneg_right hc (zpow_pos two_pos _).le
end Fpy.DigitBound
