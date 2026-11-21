-- Prove2me | Theorems.Thm_Mpfx_IsFaithfulRound_decide_lt_zero
-- name    : Mpfx.IsFaithfulRound.decide_lt_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:45:22.508238+00:00
-- url     : https://prove2.me/theorems/d338c199-05f4-42b4-a9e7-f8ed99ff5fb2
-- title:
--   Is Faithful Round: decide lt zero
-- statement:
--   A nonzero faithful rounding has the sign of `x`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L654-L664
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L654-L664

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
set_option autoImplicit true
open Mpfx

theorem Mpfx.IsFaithfulRound.decide_lt_zero {F : FiniteFormat} {x : ℝ} {y : Dyadic}
    (h : IsFaithfulRound F x y) (hy : (y : ℝ) ≠ 0) :
    decide ((y : ℚ) < 0) = decide (x < 0) := by sorry
