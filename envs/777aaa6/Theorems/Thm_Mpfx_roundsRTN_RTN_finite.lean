-- Prove2me | Theorems.Thm_Mpfx_roundsRTN_RTN_finite
-- name    : Mpfx.roundsRTN_RTN_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:52:49.614278+00:00
-- url     : https://prove2.me/theorems/323d5cd9-518a-4f9b-a24c-7ae4110ed15f
-- title:
--   Mpfx: rounds RTN RTN finite
-- statement:
--   **rnd-RTN-RTN**. Double rounding toward `−∞` collapses under `F₁ ⊆ F₂`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Basic.lean#L45-L49
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Basic.lean#L45-L49

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Format_Parity
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_DoubleRounding_Basic
set_option autoImplicit true
open Mpfx

theorem Mpfx.roundsRTN_RTN_finite {F₁ F₂ : FiniteFormat} (hsub : F₁.toFormat ⊆ F₂.toFormat)
    {x : ℝ} {z w : Dyadic}
    (hz : RoundsFinite F₂ .toNegative x z) (hw : RoundsFinite F₁ .toNegative (z : ℝ) w) :
    RoundsFinite F₁ .toNegative x w := by sorry
