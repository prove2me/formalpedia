-- Prove2me | Theorems.Thm_Mpfx_roundsRTO_RAZ_noOverflow
-- name    : Mpfx.roundsRTO_RAZ_noOverflow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:58:15.00249+00:00
-- url     : https://prove2.me/theorems/ee66b6c2-898f-492a-9e32-9b3626946c04
-- title:
--   Mpfx: rounds RTO RAZ no Overflow
-- statement:
--   **rnd-RTO-RAZ**, no overflow: if the double rounding stays in bound, so does the
--   direct rounding.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Total.lean#L595-L600
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Total.lean#L595-L600

import Definitions.Def_Mpfx_DoubleRounding_Nearest
import Definitions.Def_Mpfx_Rounding_Restrict
import Definitions.Def_Mpfx_DoubleRounding_Total
set_option autoImplicit true
open Mpfx

theorem Mpfx.roundsRTO_RAZ_noOverflow {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hnt : F₁.toFormat.Nontrivial) {x : ℝ} {z w : Dyadic}
    (hz : RoundsInBound F₂ .toOdd x z) (hw : RoundsInBound F₁ .awayZero (z : ℝ) w) :
    ¬ Overflows F₁ .awayZero x := by sorry
