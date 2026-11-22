-- Prove2me | solution 1 for Mpfx.OverflowMap.saturate_composes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:33:57.423173+00:00
-- url     : https://prove2.me/submissions/60bad0aa-d8c5-4c3a-9a03-95728d011e6e

import Definitions.Def_Mpfx_DoubleRounding_Total
import Definitions.Def_Mpfx_Rounding_Special
import Definitions.Def_Mpfx_DoubleRounding_Special
import Theorems.Thm_Mpfx_Dyadic_coe_real_neg
import Theorems.Thm_Mpfx_Dyadic_coe_real_zero
import Theorems.Thm_Mpfx_FiniteFormat_abs_le_maxFinite
import Theorems.Thm_Mpfx_FiniteFormat_le_maxFinite
import Theorems.Thm_Mpfx_FiniteFormat_saturated_eq_finite
import Theorems.Thm_Mpfx_IsFaithfulRound_decide_lt_zero
import Theorems.Thm_Mpfx_RoundsFinite_eq_zero_of_zero
import Theorems.Thm_Mpfx_RoundsFinite_isFaithfulRound
import Theorems.Thm_Mpfx_le_abs_faithful_of_le
import Theorems.Thm_Mpfx_mem_of_mem_unbounded_of_boundOK
import Theorems.Thm_Mpfx_mem_unbounded_of_mem
import Theorems.Thm_Mpfx_ne_zero_of_not_boundOK
import Theorems.Thm_Mpfx_rndUnbounded_satisfies
import Theorems.Thm_Mpfx_rnd_finite_of_roundsFinite
attribute [local simp] Mpfx.Dyadic.coe_real_neg
attribute [local simp] Mpfx.Dyadic.coe_real_zero


section
namespace Mpfx
private theorem abs_eq_maxFinite {F : FiniteFormat} (hb : F.b ≠ ⊤) {rm : RoundingMode}
    {x : ℝ} {y : Dyadic} (hx : (F.maxFinite hb : ℝ) ≤ |x|)
    (hy : RoundsFinite F.unbounded rm x y) (hby : Format.boundOK F.b y) :
    |(y : ℝ)| = F.maxFinite hb :=
  le_antisymm (F.abs_le_maxFinite hb (mem_of_mem_unbounded_of_boundOK hy.1 hby))
    (le_abs_faithful_of_le (mem_unbounded_of_mem (F.maxFinite_mem hb)) (F.maxFinite_nonneg hb)
      hx hy.isFaithfulRound)
private theorem rnd_saturate {F : FiniteFormat} (hb : F.b ≠ ⊤) {rm : RoundingMode}
    (hu : ¬ F.IsUndefined rm) (S : SpecialMap F.toFormat) {x : ℝ} {s : Bool}
    (hx : (F.maxFinite hb : ℝ) ≤ |x|) (hs : x ≠ 0 → decide (x < 0) = s) :
    rnd F S (OverflowMap.saturate F hb) rm (.finite x) = .value (F.saturated hb s) := by
  have hr := rndUnbounded_satisfies F rm x hu
  generalize rndUnbounded F rm x hu = r at hr
  rw [rnd_finite_of_roundsFinite hu hr]
  have hsign : (r : ℝ) ≠ 0 → decide ((r : ℚ) < 0) = s := fun hr0 => by
    rw [hr.isFaithfulRound.decide_lt_zero hr0]
    refine hs fun hx0 => hr0 ?_
    rw [hx0] at hr
    rw [RoundsFinite.eq_zero_of_zero hr, Dyadic.coe_real_zero]
  split_ifs with hbr
  · rw [F.saturated_eq_finite hb (abs_eq_maxFinite hb hx hr hbr) hsign]
  · rw [hsign (ne_zero_of_not_boundOK hbr)]
    rfl
end Mpfx
end

set_option autoImplicit true
open Mpfx
namespace Mpfx
namespace OverflowMap
theorem _root_.solution {F₁ F₂ : FiniteFormat}
    (hsub : F₁.toFormat ⊆ F₂.toFormat) (hb₁ : F₁.b ≠ ⊤) (hb₂ : F₂.b ≠ ⊤)
    {rm₁ : RoundingMode} (h₁u : ¬ F₁.IsUndefined rm₁) {S₁ : SpecialMap F₁.toFormat} :
    (OverflowMap.saturate F₂ hb₂).Composes S₁ (OverflowMap.saturate F₁ hb₁) rm₁ := by
  have hM := F₂.maxFinite_nonneg hb₂
  have hle : (F₁.maxFinite hb₁ : ℝ) ≤ (F₂.maxFinite hb₂ : ℝ) :=
    F₂.le_maxFinite hb₂ (hsub _ (F₁.maxFinite_mem hb₁))
  intro s
  cases s
  · change rnd F₁ S₁ _ rm₁ (.finite ((F₂.maxFinite hb₂ : Dyadic) : ℝ)) = _
    exact rnd_saturate hb₁ h₁u S₁ (by rwa [abs_of_nonneg hM])
      fun _ => decide_eq_false (not_lt.mpr hM)
  · change rnd F₁ S₁ _ rm₁ (.finite ((-F₂.maxFinite hb₂ : Dyadic) : ℝ)) = _
    rw [Dyadic.coe_real_neg]
    exact rnd_saturate hb₁ h₁u S₁ (by rwa [abs_neg, abs_of_nonneg hM])
      fun h0 => decide_eq_true (lt_of_le_of_ne (by linarith) h0)
end OverflowMap
end Mpfx
