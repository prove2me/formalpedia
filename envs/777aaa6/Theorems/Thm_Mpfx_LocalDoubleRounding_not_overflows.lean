-- Prove2me | Theorems.Thm_Mpfx_LocalDoubleRounding_not_overflows
-- name    : Mpfx.LocalDoubleRounding.not_overflows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:47:35.312646+00:00
-- url     : https://prove2.me/theorems/3df13769-3e1d-4462-943f-0f83350b1c84
-- title:
--   Local Double Rounding: not overflows
-- statement:
--   No overflow: if the double rounding stays in bound, so does the direct
--   rounding.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Total.lean#L68-L73
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Total.lean#L68-L73

import Definitions.Def_Mpfx_DoubleRounding_Nearest
import Definitions.Def_Mpfx_Rounding_Restrict
import Definitions.Def_Mpfx_DoubleRounding_Total
set_option autoImplicit true
open Mpfx

theorem Mpfx.LocalDoubleRounding.not_overflows {F₁ F₂ : FiniteFormat} {rm₁ rm₂ : RoundingMode}
    {L : ℝ → Prop} (h : LocalDoubleRounding F₁ F₂ rm₁ rm₂ L) {x : ℝ} {z w : Dyadic}
    (hz : RoundsInBound F₂ rm₂ x z) (hw : RoundsInBound F₁ rm₁ (z : ℝ) w) :
    ¬ Overflows F₁ rm₁ x := by sorry
