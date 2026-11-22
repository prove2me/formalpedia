-- Prove2me | Theorems.Thm_Fpy_DigitBound_ctxOf_below
-- name    : Fpy.DigitBound.ctxOf_below
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:22:04.208946+00:00
-- url     : https://prove2.me/theorems/18a9107c-ae20-492f-9771-8055448fa27f
-- title:
--   Digit Bound: ctx Of below
-- statement:
--   The Digit Bound construction uses the ctx Of below property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L461-L468
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L461-L468

import Definitions.Def_Fpy_DigitBound_Defs
import Definitions.Def_Fpy_DigitBound_Basic
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.ctxOf_below {n : ℕ} {d : DVal} {C : SCtx} (hd : d.Below n) (hC : ctxOf d = some C) :
    C.Below n := by sorry
