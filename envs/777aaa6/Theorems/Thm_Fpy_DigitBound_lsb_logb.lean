-- Prove2me | Theorems.Thm_Fpy_DigitBound_lsb_logb
-- name    : Fpy.DigitBound.lsb_logb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:23:10.119935+00:00
-- url     : https://prove2.me/theorems/387d3438-25b2-450a-bb20-580a1f69ee27
-- title:
--   Digit Bound: lsb logb
-- statement:
--   `logb` returns an integer.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L249-L255
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L249-L255

import Definitions.Def_Fpy_DigitBound_Basic
import Definitions.Def_Fpy_DigitBound_Digits
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.lsb_logb (u : Num) : ((0 : ℤ) : EInt) ≤ lsbOf (Num.logb u) := by sorry
