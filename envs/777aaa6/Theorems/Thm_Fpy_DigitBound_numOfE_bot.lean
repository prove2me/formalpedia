-- Prove2me | Theorems.Thm_Fpy_DigitBound_numOfE_bot
-- name    : Fpy.DigitBound.numOfE_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:16:42.88764+00:00
-- url     : https://prove2.me/theorems/912d7739-cfd7-4c3b-9989-b8a14f9e5700
-- title:
--   Digit Bound: num Of E bot
-- statement:
--   The Digit Bound construction uses the num Of E bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L341-L341
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L341-L341

import Definitions.Def_Fpy_DigitBound_Defs
import Definitions.Def_Fpy_DigitBound_Basic
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.numOfE_bot : numOfE ⊥ = .special (.inf true) := by sorry

attribute [defeq] Fpy.DigitBound.numOfE_bot
