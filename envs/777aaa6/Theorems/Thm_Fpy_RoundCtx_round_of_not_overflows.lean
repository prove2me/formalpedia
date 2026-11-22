-- Prove2me | Theorems.Thm_Fpy_RoundCtx_round_of_not_overflows
-- name    : Fpy.RoundCtx.round_of_not_overflows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:34:58.364699+00:00
-- url     : https://prove2.me/theorems/fb5eb95a-78d0-4532-a47e-ac71e57bd967
-- title:
--   Round Ctx: round of not overflows
-- statement:
--   Without overflow, rounding under `c` is rounding without its bound.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Lower.lean#L169-L173
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Lower.lean#L169-L173

import Definitions.Def_Fpy_Rewrite_Separate
import Definitions.Def_Mpfx_Rounding_Monotone
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Fpy_Rewrite_Lower
set_option autoImplicit true
open Fpy
open Mpfx
open Fpy.RoundCtx

theorem Fpy.RoundCtx.round_of_not_overflows {c c' : RoundCtx} (hF : c'.F = c.F.unbounded) (hrm : c'.rm = c.rm)
    {y : ℝ} (h : ¬ Overflows c.F c.rm y) : c'.round (.finite y) = c.round (.finite y) := by sorry
