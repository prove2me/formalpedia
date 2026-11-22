-- Prove2me | Theorems.Thm_Fpy_DigitBound_msb_add
-- name    : Fpy.DigitBound.msb_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:22:47.506939+00:00
-- url     : https://prove2.me/theorems/a3042982-459e-4d40-9e2c-e6afe2bc6c87
-- title:
--   Digit Bound: msb add
-- statement:
--   The Digit Bound construction uses the msb add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L158-L168
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L158-L168

import Definitions.Def_Fpy_DigitBound_Basic
import Definitions.Def_Fpy_DigitBound_Digits
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.msb_add (u v : Num) :
    msbOf (Num.add u v) ≤ max (msbOf u) (msbOf v) + ((1 : ℤ) : EInt) := by sorry
