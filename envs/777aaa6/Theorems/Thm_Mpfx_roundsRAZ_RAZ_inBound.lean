-- Prove2me | Theorems.Thm_Mpfx_roundsRAZ_RAZ_inBound
-- name    : Mpfx.roundsRAZ_RAZ_inBound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:57:53.922762+00:00
-- url     : https://prove2.me/theorems/ffb9270f-1c9f-4be8-8837-b1c36f77b6fb
-- title:
--   Mpfx: rounds RAZ RAZ in Bound
-- statement:
--   **rnd-RAZ-RAZ**, total form: the direct rounding overflows, or the rounding into
--   `F₂` and the double rounding stay in bound and agree with it.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Total.lean#L510-L517
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Total.lean#L510-L517

import Definitions.Def_Mpfx_DoubleRounding_Nearest
import Definitions.Def_Mpfx_Rounding_Restrict
import Definitions.Def_Mpfx_DoubleRounding_Total
set_option autoImplicit true
open Mpfx

theorem Mpfx.roundsRAZ_RAZ_inBound {F₁ F₂ : FiniteFormat}
    (hsub : F₁.toFormat ⊆ F₂.toFormat) (x : ℝ) :
    Overflows F₁ .awayZero x ∨
    (∃ z w : Dyadic, RoundsInBound F₂ .awayZero x z ∧
      RoundsInBound F₁ .awayZero (z : ℝ) w ∧
      RoundsInBound F₁ .awayZero x w) := by sorry
