-- Prove2me | Theorems.Thm_Fpy_DigitBound_digits_exp2
-- name    : Fpy.DigitBound.digits_exp2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:22:42.027992+00:00
-- url     : https://prove2.me/theorems/20e0a531-e48b-4df9-94c1-735cf19e4b89
-- title:
--   Digit Bound: digits exp2
-- statement:
--   `2ᵉ` has its only digit at `e`, or none (`2^(−∞) = 0`).
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L237-L246
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L237-L246

import Definitions.Def_Fpy_DigitBound_Basic
import Definitions.Def_Fpy_DigitBound_Digits
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.digits_exp2 (e : EInt) :
    e ≤ lsbOf (Num.exp2 (numOfE e)) ∧ msbOf (Num.exp2 (numOfE e)) ≤ e := by sorry
