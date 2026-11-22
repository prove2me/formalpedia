-- Prove2me | Theorems.Thm_Fpy_DigitBound_lsb_add
-- name    : Fpy.DigitBound.lsb_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:20:31.664187+00:00
-- url     : https://prove2.me/theorems/b3ee4a69-a665-4dbf-ad18-641b725579f5
-- title:
--   Digit Bound: lsb add
-- statement:
--   The Digit Bound construction uses the lsb add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L148-L156
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L148-L156

import Definitions.Def_Fpy_DigitBound_Basic
import Definitions.Def_Fpy_DigitBound_Digits
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.lsb_add (u v : Num) : min (lsbOf u) (lsbOf v) ≤ lsbOf (Num.add u v) := by sorry
