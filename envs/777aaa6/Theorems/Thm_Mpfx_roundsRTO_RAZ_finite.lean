-- Prove2me | Theorems.Thm_Mpfx_roundsRTO_RAZ_finite
-- name    : Mpfx.roundsRTO_RAZ_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:02:15.535012+00:00
-- url     : https://prove2.me/theorems/60abe042-b797-455e-8af5-96678dc4e12a
-- title:
--   Mpfx: rounds RTO RAZ finite
-- statement:
--   **rnd-RTO-RAZ** under the relaxed containment.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Basic.lean#L288-L294
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Basic.lean#L288-L294

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Format_Parity
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_DoubleRounding_Basic
set_option autoImplicit true
open Mpfx

theorem Mpfx.roundsRTO_RAZ_finite {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    {x : ℝ} {z w : Dyadic}
    (hz : RoundsFinite F₂ .toOdd x z) (hw : RoundsFinite F₁ .awayZero (z : ℝ) w) :
    RoundsFinite F₁ .awayZero x w := by sorry
