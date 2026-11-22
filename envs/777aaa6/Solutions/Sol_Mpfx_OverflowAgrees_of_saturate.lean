-- Prove2me | solution 1 for Mpfx.OverflowAgrees.of_saturate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:51:02.833013+00:00
-- url     : https://prove2.me/submissions/9f395f0b-4090-4a8d-baaf-9978cd63e296

import Definitions.Def_Mpfx_DoubleRounding_Total
import Definitions.Def_Mpfx_Rounding_Special
import Definitions.Def_Mpfx_DoubleRounding_Special
import Theorems.Thm_Mpfx_OverflowMap_saturate_composes
import Theorems.Thm_Mpfx_Dyadic_coe_real_lt_zero_iff
import Theorems.Thm_Mpfx_Dyadic_coe_real_zero
import Theorems.Thm_Mpfx_FiniteFormat_abs_le_maxFinite
import Theorems.Thm_Mpfx_FiniteFormat_le_maxFinite
import Theorems.Thm_Mpfx_FiniteFormat_saturated_eq_finite
import Theorems.Thm_Mpfx_IsFaithfulRound_decide_lt_zero
import Theorems.Thm_Mpfx_RoundsFinite_eq_zero_of_zero
import Theorems.Thm_Mpfx_RoundsFinite_isFaithfulRound
import Theorems.Thm_Mpfx_abs_faithful_le_of_le
import Theorems.Thm_Mpfx_boundOK_of_abs_le
import Theorems.Thm_Mpfx_eq_zero_of_coe_real_zero
import Theorems.Thm_Mpfx_le_abs_faithful_of_le
import Theorems.Thm_Mpfx_mem_of_mem_unbounded_of_boundOK
import Theorems.Thm_Mpfx_mem_unbounded_of_mem
attribute [local simp] Mpfx.Dyadic.coe_real_zero


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
private theorem maxFinite_le_abs_of_overflows {F : FiniteFormat} (hb : F.b ≠ ⊤)
    {rm : RoundingMode} {x : ℝ} (h : Overflows F rm x) : (F.maxFinite hb : ℝ) ≤ |x| := by
  obtain ⟨y, hy, hby⟩ := h
  have hM := F.maxFinite_mem hb
  refine not_lt.mp fun hlt => hby (boundOK_of_abs_le ?_ hM.2.2)
  rw [abs_of_nonneg (F.maxFinite_nonneg hb)]
  exact abs_faithful_le_of_le (mem_unbounded_of_mem hM) hlt.le hy.isFaithfulRound
private theorem abs_eq_maxFinite {F : FiniteFormat} (hb : F.b ≠ ⊤) {rm : RoundingMode}
    {x : ℝ} {y : Dyadic} (hx : (F.maxFinite hb : ℝ) ≤ |x|)
    (hy : RoundsFinite F.unbounded rm x y) (hby : Format.boundOK F.b y) :
    |(y : ℝ)| = F.maxFinite hb :=
  le_antisymm (F.abs_le_maxFinite hb (mem_of_mem_unbounded_of_boundOK hy.1 hby))
    (le_abs_faithful_of_le (mem_unbounded_of_mem (F.maxFinite_mem hb)) (F.maxFinite_nonneg hb)
      hx hy.isFaithfulRound)
private theorem saturated_eq_of_roundsInBound {F : FiniteFormat} (hb : F.b ≠ ⊤)
    {rm : RoundingMode} {x : ℝ} {y : Dyadic} (hx : (F.maxFinite hb : ℝ) ≤ |x|)
    (hy : RoundsInBound F rm x y) : F.saturated hb (decide (x < 0)) = .finite y :=
  F.saturated_eq_finite hb (abs_eq_maxFinite hb hx hy.1 hy.2) hy.1.isFaithfulRound.decide_lt_zero
end Mpfx
end

set_option autoImplicit true
open Mpfx
namespace Mpfx
namespace OverflowAgrees
theorem _root_.solution {F₁ F₂ : FiniteFormat} {S₁ : SpecialMap F₁.toFormat}
    {rm₁ rm₂ : RoundingMode} (hsub : F₁.toFormat ⊆ F₂.toFormat) (hb₁ : F₁.b ≠ ⊤)
    (hb₂ : F₂.b ≠ ⊤) (h₁u : ¬ F₁.IsUndefined rm₁) :
    OverflowAgrees F₁ S₁ (OverflowMap.saturate F₁ hb₁) rm₁
      F₂ (OverflowMap.saturate F₂ hb₂) rm₂ where
  direct x z w hz hw hov := by
    have hM := F₁.maxFinite_mem hb₁
    have hzM := le_abs_faithful_of_le (mem_unbounded_of_mem (hsub _ hM))
      (F₁.maxFinite_nonneg hb₁) (maxFinite_le_abs_of_overflows hb₁ hov) hz.1.isFaithfulRound
    exact F₁.saturated_eq_finite hb₁ (abs_eq_maxFinite hb₁ hzM hw.1 hw.2)
      (decide_lt_zero_of_double hz.1 hw.1)
  double x z y hz hov hy := by
    -- `|x| < maxFinite₁` would pin the double rounding at or below `maxFinite₁`, in bound.
    obtain ⟨w, hw, hbw⟩ := hov
    have hM := F₁.maxFinite_mem hb₁
    refine saturated_eq_of_roundsInBound hb₁ (not_lt.mp fun hlt => hbw ?_) hy
    have hzM := abs_faithful_le_of_le (mem_unbounded_of_mem (hsub _ hM)) hlt.le
      hz.1.isFaithfulRound
    refine boundOK_of_abs_le ?_ hM.2.2
    rw [abs_of_nonneg (F₁.maxFinite_nonneg hb₁)]
    exact abs_faithful_le_of_le (mem_unbounded_of_mem hM) hzM hw.isFaithfulRound
  inner x y hov hy := by
    have hM := F₁.maxFinite_mem hb₁
    rw [OverflowMap.saturate_composes hsub hb₁ hb₂ h₁u]
    exact congrArg RoundResult.value (saturated_eq_of_roundsInBound hb₁
      ((F₂.le_maxFinite hb₂ (hsub _ hM)).trans (maxFinite_le_abs_of_overflows hb₂ hov)) hy)
end OverflowAgrees
end Mpfx
