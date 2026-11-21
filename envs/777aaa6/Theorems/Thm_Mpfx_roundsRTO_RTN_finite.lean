-- Prove2me | Theorems.Thm_Mpfx_roundsRTO_RTN_finite
-- name    : Mpfx.roundsRTO_RTN_finite
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:52:44.706181+00:00
-- url     : https://prove2.me/theorems/bb1c445e-fc0b-4ad1-8107-41d1c6406b25
-- title:
--   Mpfx: rounds RTO RTN finite
-- statement:
--   **rnd-RTO-RTN** under the relaxed containment.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Basic.lean#L239-L244
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Basic.lean#L239-L244

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Format_Parity
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_DoubleRounding_Basic
set_option autoImplicit true
open Mpfx

theorem Mpfx.roundsRTO_RTN_finite {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    {x : ℝ} {z w : Dyadic}
    (hz : RoundsFinite F₂ .toOdd x z) (hw : RoundsFinite F₁ .toNegative (z : ℝ) w) :
    RoundsFinite F₁ .toNegative x w := by sorry
