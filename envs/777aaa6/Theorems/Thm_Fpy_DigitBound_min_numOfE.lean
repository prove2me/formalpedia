-- Prove2me | Theorems.Thm_Fpy_DigitBound_min_numOfE
-- name    : Fpy.DigitBound.min_numOfE
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:21:15.940177+00:00
-- url     : https://prove2.me/theorems/0cc6a188-ed95-4c9b-b369-114808348e05
-- title:
--   Digit Bound: min num Of E
-- statement:
--   The Digit Bound construction uses the min num Of E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L369-L371
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L369-L371

import Definitions.Def_Fpy_DigitBound_Defs
import Definitions.Def_Fpy_DigitBound_Basic
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.min_numOfE (a b : EInt) : Num.min (numOfE a) (numOfE b) = numOfE (min a b) := by sorry
