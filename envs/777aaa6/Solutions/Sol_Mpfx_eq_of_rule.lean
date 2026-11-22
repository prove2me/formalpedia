-- Prove2me | solution 1 for Mpfx.eq_of_rule
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:37:40.584928+00:00
-- url     : https://prove2.me/submissions/9abace96-bbf5-414a-8e59-13fd654bc2fc

import Definitions.Def_Mpfx_DoubleRounding_Nearest
import Definitions.Def_Mpfx_Rounding_Restrict
import Definitions.Def_Mpfx_DoubleRounding_Total
import Theorems.Thm_Mpfx_RoundsFinite_lift
import Theorems.Thm_Mpfx_RoundsFinite_restrict
import Theorems.Thm_Mpfx_RoundsFinite_unique


set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F₁ F₂ : FiniteFormat} {rm₁ rm₂ : RoundingMode}
    (h₁u : ¬ F₁.IsUndefined rm₁) {B : Bound}
    (rule : ∀ {x : ℝ} {z w : Dyadic}, RoundsFinite F₂.unbounded rm₂ x z →
      RoundsFinite (F₁.withBoundFF B) rm₁ (z : ℝ) w → RoundsFinite (F₁.withBoundFF B) rm₁ x w)
    {x : ℝ} {z w y : Dyadic} (hz : RoundsFinite F₂.unbounded rm₂ x z)
    (hw : RoundsFinite F₁.unbounded rm₁ (z : ℝ) w) (hy : RoundsFinite F₁.unbounded rm₁ x y)
    (hwB : Format.boundOK B w) (hyB : Format.boundOK B y) : w = y :=
  RoundsFinite.unique h₁u (RoundsFinite.lift (F := F₁.withBoundFF B)
    (rule hz (RoundsFinite.restrict (F := F₁.withBoundFF B) hw hwB)) hy hyB) hy
end Mpfx
