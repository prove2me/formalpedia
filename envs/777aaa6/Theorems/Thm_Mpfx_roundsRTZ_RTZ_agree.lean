-- Prove2me | Theorems.Thm_Mpfx_roundsRTZ_RTZ_agree
-- name    : Mpfx.roundsRTZ_RTZ_agree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:58:40.685869+00:00
-- url     : https://prove2.me/theorems/8c1404d9-a185-408d-a530-e02659499f74
-- title:
--   Mpfx: rounds RTZ RTZ agree
-- statement:
--   **rnd-RTZ-RTZ**, in bound: the double rounding agrees with the direct rounding.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Total.lean#L645-L650
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Total.lean#L645-L650

import Definitions.Def_Mpfx_DoubleRounding_Nearest
import Definitions.Def_Mpfx_Rounding_Restrict
import Definitions.Def_Mpfx_DoubleRounding_Total
set_option autoImplicit true
open Mpfx

theorem Mpfx.roundsRTZ_RTZ_agree {F₁ F₂ : FiniteFormat} (hsub : F₁.toFormat ⊆ F₂.toFormat)
    {x : ℝ} {z w y : Dyadic} (hz : RoundsInBound F₂ .toZero x z)
    (hw : RoundsInBound F₁ .toZero (z : ℝ) w) (hy : RoundsInBound F₁ .toZero x y) :
    w = y := by sorry
