-- Prove2me | Theorems.Thm_Fpy_DigitBound_msbOf_special
-- name    : Fpy.DigitBound.msbOf_special
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:18:27.312766+00:00
-- url     : https://prove2.me/theorems/dbedfbd0-9485-45fc-899b-91e78bbdef7f
-- title:
--   Digit Bound: msb Of special
-- statement:
--   The Digit Bound construction uses the msb Of special property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L127-L127
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L127-L127

import Definitions.Def_Fpy_DigitBound_Basic
import Definitions.Def_Fpy_DigitBound_Digits
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.msbOf_special (s : Special) : msbOf (.special s) = ⊤ := by sorry
