-- Prove2me | Theorems.Thm_Fpy_RoundCtx_round_finite
-- name    : Fpy.RoundCtx.round_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:06:32.866892+00:00
-- url     : https://prove2.me/theorems/897dbed8-407e-457e-8a66-9d85bd2d2cad
-- title:
--   Round Ctx: round finite
-- statement:
--   The Round Ctx construction uses the round finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Ops.lean#L236-L243
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Ops.lean#L236-L243

import Definitions.Def_Fpy_Syntax
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Fpy_Ops
set_option autoImplicit true
open Fpy
open Mpfx
open Fpy.RoundCtx
open Classical

theorem Fpy.RoundCtx.round_finite (c : RoundCtx) (y : ℝ) :
    c.round (.finite y) =
      if Format.boundOK c.F.b (rndUnbounded c.F c.rm y c.defined) then
        .finite ((rndUnbounded c.F c.rm y c.defined : Mpfx.Dyadic) : ℝ)
      else
        (c.O.map (decide ((rndUnbounded c.F c.rm y c.defined : ℚ) < 0))).toReal := by sorry
