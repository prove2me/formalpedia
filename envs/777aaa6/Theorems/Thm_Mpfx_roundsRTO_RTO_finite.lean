-- Prove2me | Theorems.Thm_Mpfx_roundsRTO_RTO_finite
-- name    : Mpfx.roundsRTO_RTO_finite
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:49:03.371767+00:00
-- url     : https://prove2.me/theorems/4c06643f-5222-41fc-bd5b-aa716f02b8ec
-- title:
--   Mpfx: rounds RTO RTO finite
-- statement:
--   **rnd-RTO-RTO** under `F₁ ⊆ F₂` and `2 ≤ F₂.p`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Basic.lean#L109-L134
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Basic.lean#L109-L134

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Format_Parity
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_DoubleRounding_Basic
set_option autoImplicit true
open Mpfx

theorem Mpfx.roundsRTO_RTO_finite {F₁ F₂ : FiniteFormat} (hsub : F₁.toFormat ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p)
    {x : ℝ} {z w' : Dyadic}
    (hz : RoundsFinite F₂ .toOdd x z) (hw : RoundsFinite F₁ .toOdd (z : ℝ) w') :
    RoundsFinite F₁ .toOdd x w' := by sorry
