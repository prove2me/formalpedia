-- Prove2me | Theorems.Thm_Fpy_DigitBound_lsb_mul
-- name    : Fpy.DigitBound.lsb_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:22:52.712167+00:00
-- url     : https://prove2.me/theorems/4ea04f40-116e-401d-be9a-99ded8c01dec
-- title:
--   Digit Bound: lsb mul
-- statement:
--   The Digit Bound construction uses the lsb mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L170-L193
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L170-L193

import Definitions.Def_Fpy_DigitBound_Basic
import Definitions.Def_Fpy_DigitBound_Digits
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.lsb_mul (u v : Num) : lsbOf u + lsbOf v ≤ lsbOf (Num.mul u v) := by sorry
