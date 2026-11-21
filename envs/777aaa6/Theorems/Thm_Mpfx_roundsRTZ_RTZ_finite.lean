-- Prove2me | Theorems.Thm_Mpfx_roundsRTZ_RTZ_finite
-- name    : Mpfx.roundsRTZ_RTZ_finite
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:49:02.97572+00:00
-- url     : https://prove2.me/theorems/ffe415cd-9b8f-4a29-a43c-425e34c0b527
-- title:
--   Mpfx: rounds RTZ RTZ finite
-- statement:
--   **rnd-RTZ-RTZ**. Double rounding toward zero collapses under `F₁ ⊆ F₂`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Basic.lean#L85-L94
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Basic.lean#L85-L94

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Format_Parity
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_DoubleRounding_Basic
set_option autoImplicit true
open Mpfx

theorem Mpfx.roundsRTZ_RTZ_finite {F₁ F₂ : FiniteFormat} (hsub : F₁.toFormat ⊆ F₂.toFormat)
    {x : ℝ} {z w : Dyadic}
    (hz : RoundsFinite F₂ .toZero x z) (hw : RoundsFinite F₁ .toZero (z : ℝ) w) :
    RoundsFinite F₁ .toZero x w := by sorry
