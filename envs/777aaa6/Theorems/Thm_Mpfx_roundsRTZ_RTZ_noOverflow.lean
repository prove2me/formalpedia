-- Prove2me | Theorems.Thm_Mpfx_roundsRTZ_RTZ_noOverflow
-- name    : Mpfx.roundsRTZ_RTZ_noOverflow
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:57:49.13582+00:00
-- url     : https://prove2.me/theorems/d7f8ab38-e72e-4bd4-9455-6546d350a4bd
-- title:
--   Mpfx: rounds RTZ RTZ no Overflow
-- statement:
--   **rnd-RTZ-RTZ**, no overflow: if the double rounding stays in bound, so does the
--   direct rounding.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Total.lean#L501-L506
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Total.lean#L501-L506

import Definitions.Def_Mpfx_DoubleRounding_Nearest
import Definitions.Def_Mpfx_Rounding_Restrict
import Definitions.Def_Mpfx_DoubleRounding_Total
set_option autoImplicit true
open Mpfx

theorem Mpfx.roundsRTZ_RTZ_noOverflow {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    {x : ℝ} {z w : Dyadic}
    (hz : RoundsInBound F₂ .toZero x z) (hw : RoundsInBound F₁ .toZero (z : ℝ) w) :
    ¬ Overflows F₁ .toZero x := by sorry
