-- Prove2me | Theorems.Thm_Fpy_DigitBound_ctxOf_admits
-- name    : Fpy.DigitBound.ctxOf_admits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:21:50.196185+00:00
-- url     : https://prove2.me/theorems/c24a2333-b662-47a0-b06c-dda34433e688
-- title:
--   Digit Bound: ctx Of admits
-- statement:
--   The Digit Bound construction uses the ctx Of admits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L431-L439
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L431-L439

import Definitions.Def_Fpy_DigitBound_Defs
import Definitions.Def_Fpy_DigitBound_Basic
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.ctxOf_admits {Ψ : List Con} {ι : Asgn} {d : DVal} {fs : List (Label × Val)}
    {C : SCtx} (hd : Describes Ψ ι d (.record fs)) (hC : ctxOf d = some C) :
    C.Admits ι (.ctx fs) := by sorry
