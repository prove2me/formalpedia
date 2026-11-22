-- Prove2me | solution 1 for Fpy.DigitBound.rndOK_any
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:48:58.873692+00:00
-- url     : https://prove2.me/submissions/44330f1c-1499-4a27-b9a6-3e6e5dcc0c82

import Definitions.Def_Fpy_DigitBound_Digits
import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Fpy_DigitBound_Table
import Theorems.Thm_Fpy_DigitBound_rnd_fresh
import Theorems.Thm_Fpy_DigitBound_lsb_round
import Theorems.Thm_Fpy_DigitBound_EInt_top_add_coe
import Theorems.Thm_Fpy_DigitBound_NumIn_eq
import Theorems.Thm_Fpy_DigitBound_eval_update
import Theorems.Thm_Fpy_DigitBound_fresh_numIn
import Theorems.Thm_Fpy_DigitBound_lsbOf_abs
import Theorems.Thm_Fpy_DigitBound_lsbOf_neg
import Theorems.Thm_Fpy_DigitBound_msbOf_abs
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
import Theorems.Thm_Mpfx_rndDown_zero
import Theorems.Thm_Mpfx_rndUp_zero
import Theorems.Thm_Mpfx_rnd_special
import Theorems.Thm_Mpfx_ulp_neg
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
attribute [local simp] Mpfx.rndDown_zero
attribute [local simp] Mpfx.rndUp_zero
attribute [local simp] Mpfx.rnd_special
attribute [local simp] Mpfx.ulp_neg



set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
variable {decode : List (Label × Val) → Option RoundCtx}
variable {n : ℕ} {l m l₁ m₁ l₂ m₂ : Term} {τ τ₁ τ₂ : Option Term}
variable {κ : Option SCtx} {Lo Ho : Term}
namespace Fpy.DigitBound
theorem _root_.solution (hl : l.Below n) (hLo : Lo.Below n) (hHo : Ho.Below n)
    (hκ : ∀ ι C r, (∀ K ∈ κ, K.Admits ι C) → C.rnd (fpy decode) = some r →
      r = id ∨ ∃ c : RoundCtx, r = c.round ∧ ImagesIn c (Lo.eval ι) (Ho.eval ι)) :
    RndOK decode κ l m n (n + 2)
      (bounds n (.min l Lo) (.max (.const ⊤) Ho) ⟨hl.mono (Nat.le_succ n), hLo.mono (Nat.le_succ n)⟩
        ⟨trivial, hHo⟩)
      (.var (n + 1)) (.var n) := by
  intro ι u C r hu hC hr
  rcases hκ ι C r hC hr with rfl | ⟨c, rfl, himg⟩
  · refine fresh_numIn _ _ ι u fun hn => ⟨le_max_of_le_left le_top, ?_⟩
    simp only [Term.eval, eval_update hl, eval_update hLo]
    exact min_le_of_left_le (hu.eq hn).1.ge
  · exact rnd_fresh (P := fun _ _ => True) (Hr := .const ⊤) (hl.mono (Nat.le_succ n)) trivial hLo
      hHo (fun _ _ => rfl) (fun ι _ _ _ _ _ hl' _ hy _ =>
        ⟨le_top, by rw [eval_update hl, ← hl']; exact lsb_round hy⟩) hu trivial himg
end Fpy.DigitBound
