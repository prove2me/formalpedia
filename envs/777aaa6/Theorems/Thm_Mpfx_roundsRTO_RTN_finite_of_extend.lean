-- Prove2me | Theorems.Thm_Mpfx_roundsRTO_RTN_finite_of_extend
-- name    : Mpfx.roundsRTO_RTN_finite_of_extend
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:52:36.120512+00:00
-- url     : https://prove2.me/theorems/57f8c463-b9d9-4fff-a8e4-3bf1a4caff3b
-- title:
--   Mpfx: rounds RTO RTN finite of extend
-- statement:
--   **rnd-RTO-RTN** under `F₁.extend 1 ⊆ F₂` and `2 ≤ F₂.p`, without the relaxed
--   bound.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Basic.lean#L203-L210
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Basic.lean#L203-L210

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Format_Parity
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_DoubleRounding_Basic
set_option autoImplicit true
open Mpfx

theorem Mpfx.roundsRTO_RTN_finite_of_extend {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.extend 1).toFormat ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p)
    {x : ℝ} {z w : Dyadic}
    (hz : RoundsFinite F₂ .toOdd x z) (hw : RoundsFinite F₁ .toNegative (z : ℝ) w) :
    RoundsFinite F₁ .toNegative x w := by sorry
