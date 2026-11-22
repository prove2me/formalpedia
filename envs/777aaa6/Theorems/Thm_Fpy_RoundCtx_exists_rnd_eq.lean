-- Prove2me | Theorems.Thm_Fpy_RoundCtx_exists_rnd_eq
-- name    : Fpy.RoundCtx.exists_rnd_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:06:21.885103+00:00
-- url     : https://prove2.me/theorems/814377a9-197b-4a23-8500-41e0b1d598cc
-- title:
--   Round Ctx: exists rnd eq
-- statement:
--   The Round Ctx construction uses the exists rnd eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Ops.lean#L222-L228
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Ops.lean#L222-L228

import Definitions.Def_Fpy_Syntax
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Fpy_Ops
set_option autoImplicit true
open Fpy
open Mpfx

theorem Fpy.RoundCtx.exists_rnd_eq (c : RoundCtx) (n : Num) :
    ∃ w, rnd c.F c.S c.O c.rm n = .value w ∧ c.round n = w.toReal := by sorry
