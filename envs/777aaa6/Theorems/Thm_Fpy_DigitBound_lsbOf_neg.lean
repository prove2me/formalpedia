-- Prove2me | Theorems.Thm_Fpy_DigitBound_lsbOf_neg
-- name    : Fpy.DigitBound.lsbOf_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:17:00.857018+00:00
-- url     : https://prove2.me/theorems/926c57ed-7a48-4cc1-b8cb-da50465e3144
-- title:
--   Digit Bound: lsb Of neg
-- statement:
--   The Digit Bound construction uses the lsb Of neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L216-L219
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L216-L219

import Definitions.Def_Fpy_DigitBound_Basic
import Definitions.Def_Fpy_DigitBound_Digits
import Theorems.Thm_Mpfx_FiniteFormat_IsEven_neg
import Theorems.Thm_Mpfx_FiniteFormat_IsOdd_neg

set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.lsbOf_neg (u : Num) : lsbOf (Num.neg u) = lsbOf u := by sorry
