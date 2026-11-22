-- Prove2me | Theorems.Thm_Fpy_DigitBound_neg_numOfE
-- name    : Fpy.DigitBound.neg_numOfE
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:21:10.738183+00:00
-- url     : https://prove2.me/theorems/06f955cc-82b9-4360-8e62-544422ea691c
-- title:
--   Digit Bound: neg num Of E
-- statement:
--   The Digit Bound construction uses the neg num Of E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L362-L363
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L362-L363

import Definitions.Def_Fpy_DigitBound_Defs
import Definitions.Def_Fpy_DigitBound_Basic
import Theorems.Thm_Mpfx_FiniteFormat_IsEven_neg
import Theorems.Thm_Mpfx_FiniteFormat_IsOdd_neg

set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.neg_numOfE (a : EInt) : Num.neg (numOfE a) = numOfE (negE a) := by sorry
