-- Prove2me | Theorems.Thm_Fpy_DigitBound_msbOf_neg
-- name    : Fpy.DigitBound.msbOf_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:17:12.789017+00:00
-- url     : https://prove2.me/theorems/2c2ec396-4168-4c76-beeb-389d94bfd37b
-- title:
--   Digit Bound: msb Of neg
-- statement:
--   The Digit Bound construction uses the msb Of neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L221-L224
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L221-L224

import Definitions.Def_Fpy_DigitBound_Basic
import Definitions.Def_Fpy_DigitBound_Digits
import Theorems.Thm_Mpfx_FiniteFormat_IsEven_neg
import Theorems.Thm_Mpfx_FiniteFormat_IsOdd_neg

set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.msbOf_neg (u : Num) : msbOf (Num.neg u) = msbOf u := by sorry
