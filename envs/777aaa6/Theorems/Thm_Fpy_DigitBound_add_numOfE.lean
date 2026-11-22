-- Prove2me | Theorems.Thm_Fpy_DigitBound_add_numOfE
-- name    : Fpy.DigitBound.add_numOfE
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:21:11.875966+00:00
-- url     : https://prove2.me/theorems/52c4fea7-abae-4941-a59d-2b33c68a5774
-- title:
--   Digit Bound: add num Of E
-- statement:
--   The Digit Bound construction uses the add num Of E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L356-L360
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L356-L360

import Definitions.Def_Fpy_DigitBound_Defs
import Definitions.Def_Fpy_DigitBound_Basic
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.add_numOfE (a b : EInt) :
    Num.add (numOfE a) (numOfE b) = nan ∨ Num.add (numOfE a) (numOfE b) = numOfE (a + b) := by sorry
