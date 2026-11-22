-- Prove2me | Theorems.Thm_Fpy_RoundCtx_round_special
-- name    : Fpy.RoundCtx.round_special
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:06:26.147387+00:00
-- url     : https://prove2.me/theorems/5f5652c5-7daa-42c6-adf9-a8ffc8f7be3a
-- title:
--   Round Ctx: round special
-- statement:
--   The Round Ctx construction uses the round special property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Ops.lean#L232-L233
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Ops.lean#L232-L233

import Definitions.Def_Fpy_Syntax
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Fpy_Ops
set_option autoImplicit true
open Fpy
open Mpfx
open Fpy.RoundCtx

theorem Fpy.RoundCtx.round_special (c : RoundCtx) (s : Special) : c.round (.special s) = (c.S.map s).toReal := by sorry
