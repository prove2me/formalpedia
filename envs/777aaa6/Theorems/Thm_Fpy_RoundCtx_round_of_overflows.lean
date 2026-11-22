-- Prove2me | Theorems.Thm_Fpy_RoundCtx_round_of_overflows
-- name    : Fpy.RoundCtx.round_of_overflows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:33:46.594829+00:00
-- url     : https://prove2.me/theorems/ecba2233-7bbc-4c40-a1f2-00576e0d0661
-- title:
--   Round Ctx: round of overflows
-- statement:
--   The Round Ctx construction uses the round of overflows property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Lower.lean#L152-L154
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Lower.lean#L152-L154

import Definitions.Def_Fpy_Rewrite_Separate
import Definitions.Def_Mpfx_Rounding_Monotone
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Fpy_Rewrite_Lower
set_option autoImplicit true
open Fpy
open Mpfx
open Fpy.RoundCtx

theorem Fpy.RoundCtx.round_of_overflows (c : RoundCtx) {y : ℝ} (h : Overflows c.F c.rm y) :
    c.round (.finite y) = (c.O.map (decide (y < 0))).toReal := by sorry
