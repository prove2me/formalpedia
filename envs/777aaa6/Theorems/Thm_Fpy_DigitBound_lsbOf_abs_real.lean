-- Prove2me | Theorems.Thm_Fpy_DigitBound_lsbOf_abs_real
-- name    : Fpy.DigitBound.lsbOf_abs_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:22:51.499291+00:00
-- url     : https://prove2.me/theorems/0a103303-90c7-4264-a63f-32ec281438d2
-- title:
--   Digit Bound: lsb Of abs real
-- statement:
--   The Digit Bound construction uses the lsb Of abs real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L120-L121
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L120-L121

import Definitions.Def_Fpy_DigitBound_Basic
import Definitions.Def_Fpy_DigitBound_Digits
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.lsbOf_abs_real (x : ℝ) : lsbOf (.finite |x|) = lsbOf (.finite x) := by sorry
