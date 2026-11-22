-- Prove2me | solution 1 for Mpfx.OverflowAgrees.of_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:36:08.362189+00:00
-- url     : https://prove2.me/submissions/eb53a572-d9ba-4ff5-8492-cdacb50e9cdf

import Definitions.Def_Mpfx_DoubleRounding_Total
import Definitions.Def_Mpfx_Rounding_Special
import Definitions.Def_Mpfx_DoubleRounding_Special
import Theorems.Thm_Mpfx_RoundsFinite_unique
import Theorems.Thm_Mpfx_overflows_iff_not_roundsInBound


set_option autoImplicit true
open Mpfx
namespace Mpfx
namespace OverflowAgrees
theorem _root_.solution {F₁ F₂ : FiniteFormat} {S₁ : SpecialMap F₁.toFormat}
    {O₁ : OverflowMap F₁.toFormat} {O₂ : OverflowMap F₂.toFormat} {rm₁ rm₂ : RoundingMode}
    (h₁u : ¬ F₁.IsUndefined rm₁) (h₂u : ¬ F₂.IsUndefined rm₂)
    (hP : ∀ x : ℝ, Overflows F₁ rm₁ x ∨
      ∃ z w : Dyadic, RoundsInBound F₂ rm₂ x z ∧ RoundsInBound F₁ rm₁ (z : ℝ) w ∧
        RoundsInBound F₁ rm₁ x w)
    (hC : ∀ (x : ℝ) (z w : Dyadic), RoundsInBound F₂ rm₂ x z →
      RoundsInBound F₁ rm₁ (z : ℝ) w → ¬ Overflows F₁ rm₁ x) :
    OverflowAgrees F₁ S₁ O₁ rm₁ F₂ O₂ rm₂ where
  direct x z w hz hw hov := absurd hov (hC x z w hz hw)
  double x z y hz hov hy := by
    rcases hP x with hov' | ⟨z', w', hz', hw', -⟩
    · exact ((overflows_iff_not_roundsInBound h₁u).mp hov' ⟨y, hy⟩).elim
    · obtain rfl := RoundsFinite.unique h₂u hz'.1 hz.1
      exact ((overflows_iff_not_roundsInBound h₁u).mp hov ⟨w', hw'⟩).elim
  inner x y hov hy := by
    rcases hP x with hov' | ⟨z', -, hz', -, -⟩
    · exact ((overflows_iff_not_roundsInBound h₁u).mp hov' ⟨y, hy⟩).elim
    · exact ((overflows_iff_not_roundsInBound h₂u).mp hov ⟨z', hz'⟩).elim
end OverflowAgrees
end Mpfx
