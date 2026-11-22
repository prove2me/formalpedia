-- Prove2me | Theorems.Thm_Fpy_DigitBound_msbOf_of_ne_zero
-- name    : Fpy.DigitBound.msbOf_of_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:17:05.662856+00:00
-- url     : https://prove2.me/theorems/35dd3c90-3c6b-4674-9439-d87f267efa89
-- title:
--   Digit Bound: msb Of of ne zero
-- statement:
--   The Digit Bound construction uses the msb Of of ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L136-L137
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L136-L137

import Definitions.Def_Fpy_DigitBound_Basic
import Definitions.Def_Fpy_DigitBound_Digits
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.msbOf_of_ne_zero {x : ℝ} (h0 : x ≠ 0) : msbOf (.finite x) = (Int.log 2 |x| : ℤ) := by sorry
