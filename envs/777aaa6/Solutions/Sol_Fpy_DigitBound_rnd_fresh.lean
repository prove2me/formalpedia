-- Prove2me | solution 1 for Fpy.DigitBound.rnd_fresh
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:40:39.712821+00:00
-- url     : https://prove2.me/submissions/8e4faee7-5c98-4a7a-9c38-d40bc8bbe531

import Definitions.Def_Fpy_DigitBound_Digits
import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Fpy_DigitBound_Table
import Theorems.Thm_Fpy_DigitBound_EInt_top_add_coe
import Theorems.Thm_Fpy_DigitBound_NumIn_eq
import Theorems.Thm_Fpy_DigitBound_eval_update
import Theorems.Thm_Fpy_DigitBound_fresh_numIn
import Theorems.Thm_Fpy_DigitBound_lsbOf_abs
import Theorems.Thm_Fpy_DigitBound_lsbOf_neg
import Theorems.Thm_Fpy_DigitBound_lsbOf_special
import Theorems.Thm_Fpy_DigitBound_lsbOf_zero
import Theorems.Thm_Fpy_DigitBound_msbOf_abs
import Theorems.Thm_Fpy_DigitBound_msbOf_neg
import Theorems.Thm_Fpy_DigitBound_msbOf_special
import Theorems.Thm_Fpy_DigitBound_msbOf_zero
import Theorems.Thm_Fpy_DigitBound_numOfE_bot
import Theorems.Thm_Fpy_DigitBound_numOfE_coe
import Theorems.Thm_Fpy_DigitBound_numOfE_top
import Theorems.Thm_Fpy_RoundCtx_round_finite
import Theorems.Thm_Fpy_RoundCtx_round_special
import Theorems.Thm_Fpy_RoundCtx_round_zero
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
import Theorems.Thm_Mpfx_rndUnbounded_satisfies
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
namespace Fpy.DigitBound
theorem _root_.solution {P : Asgn → RoundCtx → Prop} {Lr Hr Lo Ho : Term}
    (hLr : Lr.Below (n + 1)) (hHr : Hr.Below n) (hLo : Lo.Below n) (hHo : Ho.Below n)
    (htop : ∀ ι, m.eval ι = ⊤ → Hr.eval ι = ⊤)
    (hrow : ∀ ι c (x : ℝ) (y : Mpfx.Dyadic), P ι c → x ≠ 0 → lsbOf (.finite x) = l.eval ι →
      msbOf (.finite x) = m.eval ι → RoundsFinite c.F.unbounded c.rm x y → (y : ℝ) ≠ 0 →
      msbOf (.finite (y : ℝ)) ≤ Hr.eval ι ∧
        Lr.eval (Function.update ι n (msbOf (.finite (y : ℝ)))) ≤ lsbOf (.finite (y : ℝ)))
    {ι : Asgn} {u : Num} {c : RoundCtx} (hu : NumIn ι l m none u) (hP : P ι c)
    (himg : ImagesIn c (Lo.eval ι) (Ho.eval ι)) :
    ∃ ι', AgreeOut n (n + 2) ι ι' ∧
      Sat ι' (bounds n (.min Lr Lo) (.max Hr Ho) ⟨hLr, hLo.mono (Nat.le_succ n)⟩ ⟨hHr, hHo⟩) ∧
      NumIn ι' (.var (n + 1)) (.var n) none (c.round u) := by
  obtain ⟨hO, hS⟩ := himg
  refine fresh_numIn _ _ ι _ fun hw => ?_
  simp only [Term.eval, eval_update hLo]
  have ofRange : ∀ w, InRange (Lo.eval ι) (Ho.eval ι) w → w ≠ nan →
      msbOf w ≤ max (Hr.eval ι) (Ho.eval ι) ∧
        min (Lr.eval (Function.update ι n (msbOf w))) (Lo.eval ι) ≤ lsbOf w := fun w h hn => by
    obtain ⟨h₁, h₂⟩ := h.resolve_left hn
    exact ⟨h₂.trans (le_max_right _ _), (min_le_right _ _).trans h₁⟩
  rcases u with x | s
  · by_cases hx : x = 0
    · subst hx
      rw [RoundCtx.round_zero, lsbOf_zero, msbOf_zero]
      exact ⟨bot_le, le_top⟩
    obtain ⟨hl, hm⟩ := hu.eq (by simp)
    rw [RoundCtx.round_finite] at hw ⊢
    split_ifs at hw ⊢
    · by_cases hy : ((rndUnbounded c.F c.rm x c.defined : Mpfx.Dyadic) : ℝ) = 0
      · rw [hy, lsbOf_zero, msbOf_zero]
        exact ⟨bot_le, le_top⟩
      obtain ⟨h₁, h₂⟩ := hrow ι c x _ hP hx hl hm (rndUnbounded_satisfies _ _ _ _) hy
      exact ⟨h₁.trans (le_max_left _ _), (min_le_left _ _).trans h₂⟩
    · exact ofRange _ (hO _) hw
  · rw [RoundCtx.round_special] at hw ⊢
    rcases hS s with h | ⟨a, b, rfl, he⟩
    · exact ofRange _ h hw
    · obtain ⟨-, hm⟩ := hu.eq (by simp)
      rw [he, WithSpecial.toReal_special, msbOf_special, lsbOf_special, htop ι hm.symm]
      exact ⟨le_max_left _ _, le_top⟩
end Fpy.DigitBound
