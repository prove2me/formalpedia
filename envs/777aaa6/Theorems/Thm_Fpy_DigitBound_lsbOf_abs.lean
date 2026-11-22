-- Prove2me | Theorems.Thm_Fpy_DigitBound_lsbOf_abs
-- name    : Fpy.DigitBound.lsbOf_abs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:17:11.992054+00:00
-- url     : https://prove2.me/theorems/22b7d580-4065-4d17-a2bb-b2851cecbe55
-- title:
--   Digit Bound: lsb Of abs
-- statement:
--   The Digit Bound construction uses the lsb Of abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L226-L229
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L226-L229

import Definitions.Def_Fpy_DigitBound_Basic
import Definitions.Def_Fpy_DigitBound_Digits
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.lsbOf_abs (u : Num) : lsbOf (Num.abs u) = lsbOf u := by sorry
