-- Prove2me | Theorems.Thm_Mpfx_roundsRAZ_RAZ_noOverflow
-- name    : Mpfx.roundsRAZ_RAZ_noOverflow
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:58:18.595275+00:00
-- url     : https://prove2.me/theorems/7af6c7dc-d10a-4e62-9053-a8017f5b0320
-- title:
--   Mpfx: rounds RAZ RAZ no Overflow
-- statement:
--   **rnd-RAZ-RAZ**, no overflow: the double rounding is a candidate for the direct
--   one, so it bounds it. No containment is needed.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Total.lean#L521-L531
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Total.lean#L521-L531

import Definitions.Def_Mpfx_DoubleRounding_Nearest
import Definitions.Def_Mpfx_Rounding_Restrict
import Definitions.Def_Mpfx_DoubleRounding_Total
set_option autoImplicit true
open Mpfx

theorem Mpfx.roundsRAZ_RAZ_noOverflow {F₁ F₂ : FiniteFormat} {x : ℝ} {z w : Dyadic}
    (hz : RoundsInBound F₂ .awayZero x z) (hw : RoundsInBound F₁ .awayZero (z : ℝ) w) :
    ¬ Overflows F₁ .awayZero x := by sorry
