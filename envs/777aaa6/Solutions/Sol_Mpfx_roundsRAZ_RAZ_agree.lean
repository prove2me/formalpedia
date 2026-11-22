-- Prove2me | solution 1 for Mpfx.roundsRAZ_RAZ_agree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:39:57.843532+00:00
-- url     : https://prove2.me/submissions/d91226cf-630b-4032-bbec-94c37c4acbbf

import Definitions.Def_Mpfx_DoubleRounding_Nearest
import Definitions.Def_Mpfx_Rounding_Restrict
import Definitions.Def_Mpfx_DoubleRounding_Total
import Theorems.Thm_Mpfx_eq_of_rule
import Theorems.Thm_Mpfx_FiniteFormat_subset_unbounded
import Theorems.Thm_Mpfx_not_isUndefined_awayZero
import Theorems.Thm_Mpfx_roundsRAZ_RAZ_finite

section
namespace Mpfx
private theorem eq_of_inBound {F₁ F₂ : FiniteFormat} {rm₁ rm₂ : RoundingMode}
    (h₁u : ¬ F₁.IsUndefined rm₁)
    (rule : ∀ {x : ℝ} {z w : Dyadic}, RoundsFinite F₂.unbounded rm₂ x z →
      RoundsFinite F₁ rm₁ (z : ℝ) w → RoundsFinite F₁ rm₁ x w)
    {x : ℝ} {z w y : Dyadic} (hz : RoundsInBound F₂ rm₂ x z)
    (hw : RoundsInBound F₁ rm₁ (z : ℝ) w) (hy : RoundsInBound F₁ rm₁ x y) : w = y :=
  eq_of_rule (B := F₁.b) h₁u rule hz.1 hw.1 hy.1 hw.2 hy.2
end Mpfx
end

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F₁ F₂ : FiniteFormat} (hsub : F₁.toFormat ⊆ F₂.toFormat)
    {x : ℝ} {z w y : Dyadic} (hz : RoundsInBound F₂ .awayZero x z)
    (hw : RoundsInBound F₁ .awayZero (z : ℝ) w) (hy : RoundsInBound F₁ .awayZero x y) :
    w = y :=
  eq_of_inBound (not_isUndefined_awayZero F₁)
    (roundsRAZ_RAZ_finite (hsub.trans F₂.subset_unbounded)) hz hw hy
end Mpfx
