-- Prove2me | Theorems.Thm_Fpy_DigitBound_lsbOf_special
-- name    : Fpy.DigitBound.lsbOf_special
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:22:34.023207+00:00
-- url     : https://prove2.me/theorems/682c3c92-f1ee-4b83-82a1-4ee72c860a21
-- title:
--   Digit Bound: lsb Of special
-- statement:
--   The Digit Bound construction uses the lsb Of special property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L125-L125
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L125-L125

import Definitions.Def_Fpy_DigitBound_Basic
import Definitions.Def_Fpy_DigitBound_Digits
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.lsbOf_special (s : Special) : lsbOf (.special s) = ⊤ := by sorry
