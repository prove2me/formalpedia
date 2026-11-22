-- Prove2me | Theorems.Thm_Fpy_DigitBound_msbOf_mono
-- name    : Fpy.DigitBound.msbOf_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:20:03.250005+00:00
-- url     : https://prove2.me/theorems/c2839070-966e-4a81-87f8-f1d72db578e4
-- title:
--   Digit Bound: msb Of mono
-- statement:
--   The Digit Bound construction uses the msb Of mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L110-L111
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L110-L111

import Definitions.Def_Fpy_DigitBound_Basic
import Definitions.Def_Fpy_DigitBound_Digits
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.msbOf_mono {x y : ℝ} (h : |x| ≤ |y|) : msbOf (.finite x) ≤ msbOf (.finite y) := by sorry
