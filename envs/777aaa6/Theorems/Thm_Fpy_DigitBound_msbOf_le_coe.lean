-- Prove2me | Theorems.Thm_Fpy_DigitBound_msbOf_le_coe
-- name    : Fpy.DigitBound.msbOf_le_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:17:17.179944+00:00
-- url     : https://prove2.me/theorems/2b0b9a52-f1eb-44dc-974d-037ffad37a33
-- title:
--   Digit Bound: msb Of le coe
-- statement:
--   The Digit Bound construction uses the msb Of le coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L103-L108
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L103-L108

import Definitions.Def_Fpy_DigitBound_Basic
import Definitions.Def_Fpy_DigitBound_Digits
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.msbOf_le_coe {x : ℝ} {k : ℤ} : msbOf (.finite x) ≤ k ↔ |x| < 2 ^ (k + 1) := by sorry
