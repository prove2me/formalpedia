-- Prove2me | Theorems.Thm_Fpy_DigitBound_max_numOfE
-- name    : Fpy.DigitBound.max_numOfE
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:21:17.590185+00:00
-- url     : https://prove2.me/theorems/09e63ae5-f81a-4dc4-886b-a8991a92eb53
-- title:
--   Digit Bound: max num Of E
-- statement:
--   The Digit Bound construction uses the max num Of E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L365-L367
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L365-L367

import Definitions.Def_Fpy_DigitBound_Defs
import Definitions.Def_Fpy_DigitBound_Basic
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.max_numOfE (a b : EInt) : Num.max (numOfE a) (numOfE b) = numOfE (max a b) := by sorry
