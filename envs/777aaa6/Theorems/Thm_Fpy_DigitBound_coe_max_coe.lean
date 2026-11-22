-- Prove2me | Theorems.Thm_Fpy_DigitBound_coe_max_coe
-- name    : Fpy.DigitBound.coe_max_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:19:32.954879+00:00
-- url     : https://prove2.me/theorems/87b13ee1-61a6-4a49-b3a5-c6c8df78c67f
-- title:
--   Digit Bound: coe max coe
-- statement:
--   The Digit Bound construction uses the coe max coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L350-L351
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L350-L351

import Definitions.Def_Fpy_DigitBound_Defs
import Definitions.Def_Fpy_DigitBound_Basic
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.coe_max_coe (a b : ℤ) : max (a : EInt) (b : EInt) = ((max a b : ℤ) : EInt) := by sorry
