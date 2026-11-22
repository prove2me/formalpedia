-- Prove2me | Theorems.Thm_Mpfx_roundsRTZ_RTZ_inBound
-- name    : Mpfx.roundsRTZ_RTZ_inBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:58:06.814036+00:00
-- url     : https://prove2.me/theorems/86a4c20f-20a1-4ea3-8092-2af621b77537
-- title:
--   Mpfx: rounds RTZ RTZ in Bound
-- statement:
--   **rnd-RTZ-RTZ**, total form: the direct rounding overflows, or the rounding into
--   `F₂` and the double rounding stay in bound and agree with it.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Total.lean#L489-L497
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Total.lean#L489-L497

import Definitions.Def_Mpfx_DoubleRounding_Nearest
import Definitions.Def_Mpfx_Rounding_Restrict
import Definitions.Def_Mpfx_DoubleRounding_Total
set_option autoImplicit true
open Mpfx

theorem Mpfx.roundsRTZ_RTZ_inBound {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (x : ℝ) :
    Overflows F₁ .toZero x ∨
    (∃ z w : Dyadic, RoundsInBound F₂ .toZero x z ∧
      RoundsInBound F₁ .toZero (z : ℝ) w ∧
      RoundsInBound F₁ .toZero x w) := by sorry
