-- Prove2me | Theorems.Thm_Mpfx_roundsRTO_RTZ_noOverflow
-- name    : Mpfx.roundsRTO_RTZ_noOverflow
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:58:17.889116+00:00
-- url     : https://prove2.me/theorems/e09ab7f0-85d6-48bc-bf04-63e056f0b240
-- title:
--   Mpfx: rounds RTO RTZ no Overflow
-- statement:
--   **rnd-RTO-RTZ**, no overflow: if the double rounding stays in bound, so does the
--   direct rounding.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Total.lean#L572-L577
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Total.lean#L572-L577

import Definitions.Def_Mpfx_DoubleRounding_Nearest
import Definitions.Def_Mpfx_Rounding_Restrict
import Definitions.Def_Mpfx_DoubleRounding_Total
set_option autoImplicit true
open Mpfx

theorem Mpfx.roundsRTO_RTZ_noOverflow {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hnt : F₁.toFormat.Nontrivial) {x : ℝ} {z w : Dyadic}
    (hz : RoundsInBound F₂ .toOdd x z) (hw : RoundsInBound F₁ .toZero (z : ℝ) w) :
    ¬ Overflows F₁ .toZero x := by sorry
