-- Prove2me | Theorems.Thm_Fpy_DigitBound_lsbOf_neg_real
-- name    : Fpy.DigitBound.lsbOf_neg_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:20:37.15109+00:00
-- url     : https://prove2.me/theorems/91c4818b-cef2-4de8-8664-277747fd7611
-- title:
--   Digit Bound: lsb Of neg real
-- statement:
--   The Digit Bound construction uses the lsb Of neg real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L113-L118
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L113-L118

import Definitions.Def_Fpy_DigitBound_Basic
import Definitions.Def_Fpy_DigitBound_Digits
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.lsbOf_neg_real (x : ℝ) : lsbOf (.finite (-x)) = lsbOf (.finite x) := by sorry
