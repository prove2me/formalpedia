-- Prove2me | Theorems.Thm_Fpy_RoundCtx_round_zero
-- name    : Fpy.RoundCtx.round_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:06:31.479927+00:00
-- url     : https://prove2.me/theorems/54888909-d22a-4a85-8de8-751a0dd6eae4
-- title:
--   Round Ctx: round zero
-- statement:
--   The Round Ctx construction uses the round zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Ops.lean#L245-L249
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Ops.lean#L245-L249

import Definitions.Def_Fpy_Syntax
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Fpy_Ops
set_option autoImplicit true
open Fpy
open Mpfx
open Fpy.RoundCtx

theorem Fpy.RoundCtx.round_zero (c : RoundCtx) : c.round (.finite 0) = .finite 0 := by sorry
