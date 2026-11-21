-- Prove2me | Theorems.Thm_Mpfx_roundsRAZ_RAZ_finite
-- name    : Mpfx.roundsRAZ_RAZ_finite
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:54:15.245225+00:00
-- url     : https://prove2.me/theorems/41dd77e1-cb59-4933-9d0f-dde90c8e3eac
-- title:
--   Mpfx: rounds RAZ RAZ finite
-- statement:
--   **rnd-RAZ-RAZ**. Double rounding away from zero collapses under `F₁ ⊆ F₂`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Basic.lean#L97-L106
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Basic.lean#L97-L106

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Format_Parity
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_DoubleRounding_Basic
set_option autoImplicit true
open Mpfx

theorem Mpfx.roundsRAZ_RAZ_finite {F₁ F₂ : FiniteFormat} (hsub : F₁.toFormat ⊆ F₂.toFormat)
    {x : ℝ} {z w : Dyadic}
    (hz : RoundsFinite F₂ .awayZero x z) (hw : RoundsFinite F₁ .awayZero (z : ℝ) w) :
    RoundsFinite F₁ .awayZero x w := by sorry
