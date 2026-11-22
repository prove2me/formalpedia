-- Prove2me | Theorems.Thm_Fpy_DigitBound_lsbOf_zero
-- name    : Fpy.DigitBound.lsbOf_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:20:34.30877+00:00
-- url     : https://prove2.me/theorems/ec467ac6-a957-4c3a-949a-3e4ca30175d9
-- title:
--   Digit Bound: lsb Of zero
-- statement:
--   The Digit Bound construction uses the lsb Of zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L129-L129
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L129-L129

import Definitions.Def_Fpy_DigitBound_Basic
import Definitions.Def_Fpy_DigitBound_Digits
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.lsbOf_zero : lsbOf (.finite 0) = ⊤ := by sorry
