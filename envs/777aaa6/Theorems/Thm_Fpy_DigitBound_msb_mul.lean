-- Prove2me | Theorems.Thm_Fpy_DigitBound_msb_mul
-- name    : Fpy.DigitBound.msb_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:22:39.258638+00:00
-- url     : https://prove2.me/theorems/2a6c8004-0ba5-4799-8229-d77835c411bd
-- title:
--   Digit Bound: msb mul
-- statement:
--   The Digit Bound construction uses the msb mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L195-L214
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L195-L214

import Definitions.Def_Fpy_DigitBound_Basic
import Definitions.Def_Fpy_DigitBound_Digits
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.msb_mul {u v : Num} (hn : Num.mul u v ≠ nan) :
    msbOf (Num.mul u v) ≤ msbOf u + msbOf v + ((1 : ℤ) : EInt) := by sorry
