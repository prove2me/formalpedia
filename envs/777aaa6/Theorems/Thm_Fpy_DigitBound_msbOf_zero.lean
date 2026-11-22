-- Prove2me | Theorems.Thm_Fpy_DigitBound_msbOf_zero
-- name    : Fpy.DigitBound.msbOf_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:18:26.122591+00:00
-- url     : https://prove2.me/theorems/063df76a-31d0-4708-ae67-8be781d99763
-- title:
--   Digit Bound: msb Of zero
-- statement:
--   The Digit Bound construction uses the msb Of zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L131-L131
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L131-L131

import Definitions.Def_Fpy_DigitBound_Basic
import Definitions.Def_Fpy_DigitBound_Digits
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.msbOf_zero : msbOf (.finite 0) = ⊥ := by sorry
