-- Prove2me | Theorems.Thm_Fpy_DigitBound_DEnv_Holds_single
-- name    : Fpy.DigitBound.DEnv.Holds.single
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:17:41.8787+00:00
-- url     : https://prove2.me/theorems/a4444625-1204-4c19-b620-562f09c62b1b
-- title:
--   Holds: single
-- statement:
--   The Holds construction uses the single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L270-L277
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L270-L277

import Definitions.Def_Fpy_DigitBound_Defs
import Definitions.Def_Fpy_DigitBound_Basic
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx

theorem Fpy.DigitBound.DEnv.Holds.single {Ψ : List Con} {ι : Asgn} {y : Var} {d : DVal} {v : Val}
    (hd : Describes Ψ ι d v) : (DEnv.single y d).Holds Ψ ι (Store.single y v) := by sorry
