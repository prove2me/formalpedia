-- Prove2me | Theorems.Thm_Fpy_DigitBound_lsbOf_of_lsbAt
-- name    : Fpy.DigitBound.lsbOf_of_lsbAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:22:18.930038+00:00
-- url     : https://prove2.me/theorems/4504ac84-6319-42e9-a7b0-924c6e0f18f5
-- title:
--   Digit Bound: lsb Of of lsb At
-- statement:
--   The Digit Bound construction uses the lsb Of of lsb At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L65-L69
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L65-L69

import Definitions.Def_Fpy_DigitBound_Basic
import Definitions.Def_Fpy_DigitBound_Digits
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.lsbOf_of_lsbAt {x : ℝ} {k : ℤ} (h : LsbAt x k) : lsbOf (.finite x) = k := by sorry
