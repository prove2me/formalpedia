-- Prove2me | Theorems.Thm_Mpfx_roundsRTO_RTZ_finite
-- name    : Mpfx.roundsRTO_RTZ_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:02:21.75067+00:00
-- url     : https://prove2.me/theorems/206c0a88-59a7-45c7-98c2-c6749cd7b714
-- title:
--   Mpfx: rounds RTO RTZ finite
-- statement:
--   **rnd-RTO-RTZ** under the relaxed containment.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Basic.lean#L267-L273
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Basic.lean#L267-L273

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Format_Parity
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_DoubleRounding_Basic
set_option autoImplicit true
open Mpfx

theorem Mpfx.roundsRTO_RTZ_finite {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    {x : ℝ} {z w : Dyadic}
    (hz : RoundsFinite F₂ .toOdd x z) (hw : RoundsFinite F₁ .toZero (z : ℝ) w) :
    RoundsFinite F₁ .toZero x w := by sorry
