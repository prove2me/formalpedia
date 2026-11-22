-- Prove2me | Theorems.Thm_Fpy_RoundCtx_round_unbounded
-- name    : Fpy.RoundCtx.round_unbounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:33:49.767796+00:00
-- url     : https://prove2.me/theorems/1ffdee10-6a7e-47c2-91c7-2fee878fe41d
-- title:
--   Round Ctx: round unbounded
-- statement:
--   A context into `F` without its bound rounds without overflow.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Lower.lean#L157-L166
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Lower.lean#L157-L166

import Definitions.Def_Fpy_Rewrite_Separate
import Definitions.Def_Mpfx_Rounding_Monotone
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Fpy_Rewrite_Lower
set_option autoImplicit true
open Fpy
open Mpfx
open Fpy.RoundCtx

theorem Fpy.RoundCtx.round_unbounded {c c' : RoundCtx} (hF : c'.F = c.F.unbounded) (hrm : c'.rm = c.rm)
    (y : ℝ) :
    c'.round (.finite y) = .finite ((rndUnbounded c.F c.rm y c.defined : Mpfx.Dyadic) : ℝ) := by sorry
