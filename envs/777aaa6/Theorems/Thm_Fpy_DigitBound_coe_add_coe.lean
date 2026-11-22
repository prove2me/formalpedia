-- Prove2me | Theorems.Thm_Fpy_DigitBound_coe_add_coe
-- name    : Fpy.DigitBound.coe_add_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:16:10.206959+00:00
-- url     : https://prove2.me/theorems/a975a819-14e3-4bf8-a084-ff390eda7907
-- title:
--   Digit Bound: coe add coe
-- statement:
--   The Digit Bound construction uses the coe add coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L345-L348
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L345-L348

import Definitions.Def_Fpy_DigitBound_Defs
import Definitions.Def_Fpy_DigitBound_Basic
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.coe_add_coe (a b : ℤ) : ((a : EInt) + (b : EInt)) = ((a + b : ℤ) : EInt) := by sorry
