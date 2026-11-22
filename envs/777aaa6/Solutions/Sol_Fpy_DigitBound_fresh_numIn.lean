-- Prove2me | solution 1 for Fpy.DigitBound.fresh_numIn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:17:15.702836+00:00
-- url     : https://prove2.me/submissions/8b223b30-2915-4d5d-8f35-d3d62c1d3ef0

import Definitions.Def_Fpy_DigitBound_Defs
import Definitions.Def_Fpy_DigitBound_Basic
import Theorems.Thm_Fpy_DigitBound_Con_P_lower
import Theorems.Thm_Fpy_DigitBound_Con_P_upper
import Theorems.Thm_Fpy_DigitBound_Term_eval_congr
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
local notation "nan" => (WithSpecial.special Special.nan : Num)
namespace Fpy.DigitBound
theorem _root_.solution {n : ℕ} {Lo Hi : Term} (hLo : Lo.Below (n + 1)) (hHi : Hi.Below n)
    (ι : Asgn) (w : Num)
    (h : w ≠ nan → msbOf w ≤ Hi.eval ι ∧ Lo.eval (Function.update ι n (msbOf w)) ≤ lsbOf w) :
    ∃ ι', AgreeOut n (n + 2) ι ι' ∧ Sat ι' (bounds n Lo Hi hLo hHi) ∧
      NumIn ι' (.var (n + 1)) (.var n) none w := by
  have key : ∀ a b : EInt, b ≤ Hi.eval ι → Lo.eval (Function.update ι n b) ≤ a →
      (w = nan ∨ a = lsbOf w ∧ b = msbOf w) →
      ∃ ι', AgreeOut n (n + 2) ι ι' ∧ Sat ι' (bounds n Lo Hi hLo hHi) ∧
        NumIn ι' (.var (n + 1)) (.var n) none w := by
    intro a b hb ha hw
    let ι₁ := Function.update ι n b
    let ι' := Function.update ι₁ (n + 1) a
    have e₁ : Agree n ι ι₁ := fun x hx => (Function.update_of_ne hx.ne _ _).symm
    have e' : Agree (n + 1) ι₁ ι' := fun x hx => (Function.update_of_ne hx.ne _ _).symm
    have hn : ι' n = b := by simp [ι', ι₁]
    have hn1 : ι' (n + 1) = a := by simp [ι']
    refine ⟨ι', fun x hx => ?_, fun c hc => ?_, ?_⟩
    · simp only [ι', ι₁]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    · simp only [bounds, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · simp only [Con.P_upper, hn]
        rwa [← Term.eval_congr (e₁.trans (e'.mono (Nat.le_succ n))) hHi]
      · simp only [Con.P_lower, hn1]
        rwa [← Term.eval_congr e' hLo]
    · rcases hw with hw | ⟨rfl, rfl⟩
      · exact .inl hw
      · exact .inr ⟨hn1.symm, hn.symm, fun _ h => absurd h (by simp)⟩
  by_cases hw : w = nan
  · exact key ⊤ ⊥ bot_le le_top (.inl hw)
  · exact key _ _ (h hw).1 (h hw).2 (.inr ⟨rfl, rfl⟩)
end Fpy.DigitBound
