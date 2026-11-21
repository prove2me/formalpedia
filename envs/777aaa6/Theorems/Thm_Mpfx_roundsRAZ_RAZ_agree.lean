-- Prove2me | Theorems.Thm_Mpfx_roundsRAZ_RAZ_agree
-- name    : Mpfx.roundsRAZ_RAZ_agree
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:58:43.004402+00:00
-- url     : https://prove2.me/theorems/38192abf-1e69-4a7c-a6d1-85dca1685769
-- title:
--   Mpfx: rounds RAZ RAZ agree
-- statement:
--   **rnd-RAZ-RAZ**, in bound: the double rounding agrees with the direct rounding.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Total.lean#L653-L658
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Total.lean#L653-L658

import Definitions.Def_Mpfx_DoubleRounding_Nearest
import Definitions.Def_Mpfx_Rounding_Restrict
import Definitions.Def_Mpfx_DoubleRounding_Total
set_option autoImplicit true
open Mpfx

theorem Mpfx.roundsRAZ_RAZ_agree {F₁ F₂ : FiniteFormat} (hsub : F₁.toFormat ⊆ F₂.toFormat)
    {x : ℝ} {z w y : Dyadic} (hz : RoundsInBound F₂ .awayZero x z)
    (hw : RoundsInBound F₁ .awayZero (z : ℝ) w) (hy : RoundsInBound F₁ .awayZero x y) :
    w = y := by sorry
