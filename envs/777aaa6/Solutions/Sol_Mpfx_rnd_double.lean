-- Prove2me | solution 1 for Mpfx.rnd_double
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:33:54.061542+00:00
-- url     : https://prove2.me/submissions/aed151c3-4926-44ea-b2bf-5957ef0cf3f7

import Definitions.Def_Mpfx_DoubleRounding_Total
import Definitions.Def_Mpfx_Rounding_Special
import Definitions.Def_Mpfx_DoubleRounding_Special
import Theorems.Thm_Mpfx_Dyadic_coe_abs
import Theorems.Thm_Mpfx_Dyadic_coe_half
import Theorems.Thm_Mpfx_Dyadic_coe_ofIntZpow
import Theorems.Thm_Mpfx_Dyadic_coe_rat_abs
import Theorems.Thm_Mpfx_Dyadic_coe_rat_half
import Theorems.Thm_Mpfx_Dyadic_coe_rat_ofIntZpow
import Theorems.Thm_Mpfx_Dyadic_coe_real_add
import Theorems.Thm_Mpfx_Dyadic_coe_real_inj
import Theorems.Thm_Mpfx_Dyadic_coe_real_lt_zero_iff
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
import Theorems.Thm_Mpfx_IsFaithfulRound_decide_lt_zero
import Theorems.Thm_Mpfx_RoundsFinite_eq_zero_of_zero
import Theorems.Thm_Mpfx_RoundsFinite_isFaithfulRound
import Theorems.Thm_Mpfx_Special_neg_neg
import Theorems.Thm_Mpfx_WithSpecial_neg_finite
import Theorems.Thm_Mpfx_WithSpecial_neg_neg
import Theorems.Thm_Mpfx_WithSpecial_neg_special
import Theorems.Thm_Mpfx_WithSpecial_toReal_finite
import Theorems.Thm_Mpfx_WithSpecial_toReal_special
import Theorems.Thm_Mpfx_eq_zero_of_coe_real_zero
import Theorems.Thm_Mpfx_ne_zero_of_not_boundOK
import Theorems.Thm_Mpfx_rndUnbounded_satisfies
import Theorems.Thm_Mpfx_rnd_finite_of_roundsFinite
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


section
namespace Mpfx
private theorem decide_lt_zero_of_double {F₁ F₂ : FiniteFormat} {rm₁ rm₂ : RoundingMode}
    {x : ℝ} {z w : Dyadic} (hz : RoundsFinite F₂.unbounded rm₂ x z)
    (hw : RoundsFinite F₁.unbounded rm₁ (z : ℝ) w) (hw0 : (w : ℝ) ≠ 0) :
    decide ((w : ℚ) < 0) = decide (x < 0) := by
  have hz0 : (z : ℝ) ≠ 0 := fun h0 => hw0 (by
    rw [eq_zero_of_coe_real_zero h0, Dyadic.coe_real_zero] at hw
    rw [RoundsFinite.eq_zero_of_zero hw, Dyadic.coe_real_zero])
  rw [hw.isFaithfulRound.decide_lt_zero hw0, ← hz.isFaithfulRound.decide_lt_zero hz0]
  exact decide_eq_decide.mpr (Dyadic.coe_real_lt_zero_iff z)
end Mpfx
end

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F₁ F₂ : FiniteFormat} {S₁ : SpecialMap F₁.toFormat}
    {O₁ : OverflowMap F₁.toFormat} {S₂ : SpecialMap F₂.toFormat}
    {O₂ : OverflowMap F₂.toFormat} {rm₁ rm₂ : RoundingMode}
    (h₁u : ¬ F₁.IsUndefined rm₁)
    (hA : ∀ (x : ℝ) (z w y : Dyadic), RoundsInBound F₂ rm₂ x z →
      RoundsInBound F₁ rm₁ (z : ℝ) w → RoundsInBound F₁ rm₁ x y → w = y)
    (hov : OverflowAgrees F₁ S₁ O₁ rm₁ F₂ O₂ rm₂)
    (hS : S₂.Composes S₁ O₁ rm₁) (hO : O₂.Composes S₁ O₁ rm₁)
    {v : WithSpecial ℝ} {u : WithSpecial Dyadic} (hu : rnd F₂ S₂ O₂ rm₂ v = .value u) :
    rnd F₁ S₁ O₁ rm₁ u.toReal = rnd F₁ S₁ O₁ rm₁ v := by
  cases v with
  | special t =>
    rw [rnd_special] at hu
    obtain rfl := RoundResult.value.inj hu
    rw [hS t, rnd_special]
  | finite x =>
    have h₂u : ¬ F₂.IsUndefined rm₂ := fun h => by
      simp only [rnd, dif_pos h] at hu
      exact RoundResult.noConfusion hu
    have hz := rndUnbounded_satisfies F₂ rm₂ x h₂u
    have hy := rndUnbounded_satisfies F₁ rm₁ x h₁u
    generalize rndUnbounded F₂ rm₂ x h₂u = z at hz
    generalize rndUnbounded F₁ rm₁ x h₁u = y at hy
    rw [rnd_finite_of_roundsFinite h₂u hz] at hu
    rw [rnd_finite_of_roundsFinite h₁u hy]
    -- An overflowing rounding of `x` carries the sign of `x`.
    have hsgn : ∀ {F : FiniteFormat} {rm : RoundingMode} {d : Dyadic},
        RoundsFinite F.unbounded rm x d → ¬ Format.boundOK F.b d →
        decide ((d : ℚ) < 0) = decide (x < 0) := fun hd hbd =>
      hd.isFaithfulRound.decide_lt_zero (ne_zero_of_not_boundOK hbd)
    by_cases hbz : Format.boundOK F₂.b z
    · rw [if_pos hbz] at hu
      obtain rfl := RoundResult.value.inj hu
      have hw := rndUnbounded_satisfies F₁ rm₁ (z : ℝ) h₁u
      generalize rndUnbounded F₁ rm₁ (z : ℝ) h₁u = w at hw
      rw [WithSpecial.toReal_finite, rnd_finite_of_roundsFinite h₁u hw]
      by_cases hbw : Format.boundOK F₁.b w
      · rw [if_pos hbw]
        by_cases hby : Format.boundOK F₁.b y
        · rw [if_pos hby, hA x z w y ⟨hz, hbz⟩ ⟨hw, hbw⟩ ⟨hy, hby⟩]
        · rw [if_neg hby, hsgn hy hby, hov.direct x z w ⟨hz, hbz⟩ ⟨hw, hbw⟩ ⟨y, hy, hby⟩]
      · rw [if_neg hbw, decide_lt_zero_of_double hz hw (ne_zero_of_not_boundOK hbw)]
        by_cases hby : Format.boundOK F₁.b y
        · rw [if_pos hby, hov.double x z y ⟨hz, hbz⟩ ⟨w, hw, hbw⟩ ⟨hy, hby⟩]
        · rw [if_neg hby, hsgn hy hby]
    · rw [if_neg hbz] at hu
      obtain rfl := RoundResult.value.inj hu
      rw [hsgn hz hbz]
      by_cases hby : Format.boundOK F₁.b y
      · rw [if_pos hby, hov.inner x y ⟨z, hz, hbz⟩ ⟨hy, hby⟩]
      · rw [hO, if_neg hby, hsgn hy hby]
end Mpfx
