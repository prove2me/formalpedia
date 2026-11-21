-- Prove2me | Theorems.Thm_Mpfx_roundsRTP_RTP_finite
-- name    : Mpfx.roundsRTP_RTP_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:52:30.397992+00:00
-- url     : https://prove2.me/theorems/40a6d49e-d419-4ce2-85e4-f7f9ee0d1ed8
-- title:
--   Mpfx: rounds RTP RTP finite
-- statement:
--   **rnd-RTP-RTP**. Double rounding toward `+∞` collapses under `F₁ ⊆ F₂`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Basic.lean#L52-L56
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Basic.lean#L52-L56

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Format_Parity
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_DoubleRounding_Basic
set_option autoImplicit true
open Mpfx

theorem Mpfx.roundsRTP_RTP_finite {F₁ F₂ : FiniteFormat} (hsub : F₁.toFormat ⊆ F₂.toFormat)
    {x : ℝ} {z w : Dyadic}
    (hz : RoundsFinite F₂ .toPositive x z) (hw : RoundsFinite F₁ .toPositive (z : ℝ) w) :
    RoundsFinite F₁ .toPositive x w := by sorry
