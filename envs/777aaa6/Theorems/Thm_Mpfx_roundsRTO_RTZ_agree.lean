-- Prove2me | Theorems.Thm_Mpfx_roundsRTO_RTZ_agree
-- name    : Mpfx.roundsRTO_RTZ_agree
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:58:50.882055+00:00
-- url     : https://prove2.me/theorems/2ef996b0-df94-4d0e-b511-a5b0ed43d5c1
-- title:
--   Mpfx: rounds RTO RTZ agree
-- statement:
--   **rnd-RTO-RTZ**, in bound: the double rounding agrees with the direct rounding.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Total.lean#L669-L675
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Total.lean#L669-L675

import Definitions.Def_Mpfx_DoubleRounding_Nearest
import Definitions.Def_Mpfx_Rounding_Restrict
import Definitions.Def_Mpfx_DoubleRounding_Total
set_option autoImplicit true
open Mpfx

theorem Mpfx.roundsRTO_RTZ_agree {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.extend 1).toFormat ⊆ F₂.toFormat) (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p)
    {x : ℝ} {z w y : Dyadic} (hz : RoundsInBound F₂ .toOdd x z)
    (hw : RoundsInBound F₁ .toZero (z : ℝ) w) (hy : RoundsInBound F₁ .toZero x y) :
    w = y := by sorry
