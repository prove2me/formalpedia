-- Prove2me | Theorems.Thm_Mpfx_localDoubleRounding_of_below
-- name    : Mpfx.localDoubleRounding_of_below
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:53:12.524979+00:00
-- url     : https://prove2.me/theorems/3bb0bd61-650f-41c7-9a03-df22eaaca195
-- title:
--   Mpfx: local Double Rounding of below
-- statement:
--   Locality below a value of `F₁`, given the two pins.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Total.lean#L101-L126
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Total.lean#L101-L126

import Definitions.Def_Mpfx_DoubleRounding_Nearest
import Definitions.Def_Mpfx_Rounding_Restrict
import Definitions.Def_Mpfx_DoubleRounding_Total
set_option autoImplicit true
open Mpfx

theorem Mpfx.localDoubleRounding_of_below {F₁ F₂ : FiniteFormat} {rm₁ rm₂ : RoundingMode}
    (h₁u : ¬ F₁.IsUndefined rm₁) {B : Bound}
    (hmem : ∀ {T : Dyadic}, T ∈ F₁.unbounded → Format.boundOK B T → T ∈ F₂)
    (rule : ∀ {T : NonNegDyadic}, T.val ∈ F₁.unbounded → Format.boundOK B T.val →
      ∀ {x : ℝ} {z w : Dyadic}, RoundsFinite F₂.unbounded rm₂ x z →
        RoundsFinite (F₁.withBoundFF T) rm₁ (z : ℝ) w →
        RoundsFinite (F₁.withBoundFF T) rm₁ x w)
    (pin_direct : ∀ {x : ℝ} {y : Dyadic}, RoundsInBound F₁ rm₁ x y → BelowValue F₁ B x)
    (pin_double : ∀ {x : ℝ} {z w : Dyadic}, RoundsInBound F₂ rm₂ x z →
      RoundsInBound F₁ rm₁ (z : ℝ) w → BelowValue F₁ B x) :
    LocalDoubleRounding F₁ F₂ rm₁ rm₂ (BelowValue F₁ B) := by sorry
