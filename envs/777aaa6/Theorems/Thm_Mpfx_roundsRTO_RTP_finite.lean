-- Prove2me | Theorems.Thm_Mpfx_roundsRTO_RTP_finite
-- name    : Mpfx.roundsRTO_RTP_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:53:26.388429+00:00
-- url     : https://prove2.me/theorems/126910b2-f07a-424b-b642-291aed74bfe2
-- title:
--   Mpfx: rounds RTO RTP finite
-- statement:
--   **rnd-RTO-RTP** under the relaxed containment.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Basic.lean#L247-L252
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Basic.lean#L247-L252

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Format_Parity
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_DoubleRounding_Basic
set_option autoImplicit true
open Mpfx

theorem Mpfx.roundsRTO_RTP_finite {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    {x : ℝ} {z w : Dyadic}
    (hz : RoundsFinite F₂ .toOdd x z) (hw : RoundsFinite F₁ .toPositive (z : ℝ) w) :
    RoundsFinite F₁ .toPositive x w := by sorry
