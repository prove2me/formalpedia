-- Prove2me | Theorems.Thm_Fpy_DigitBound_msbOf_abs
-- name    : Fpy.DigitBound.msbOf_abs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:17:18.55645+00:00
-- url     : https://prove2.me/theorems/fec8fdd9-87b1-4586-b60c-c2e583f88dab
-- title:
--   Digit Bound: msb Of abs
-- statement:
--   The Digit Bound construction uses the msb Of abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L231-L234
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L231-L234

import Definitions.Def_Fpy_DigitBound_Basic
import Definitions.Def_Fpy_DigitBound_Digits
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.msbOf_abs (u : Num) : msbOf (Num.abs u) = msbOf u := by sorry
