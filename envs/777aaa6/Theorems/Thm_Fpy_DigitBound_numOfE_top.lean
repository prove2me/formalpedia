-- Prove2me | Theorems.Thm_Fpy_DigitBound_numOfE_top
-- name    : Fpy.DigitBound.numOfE_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:16:39.594781+00:00
-- url     : https://prove2.me/theorems/68aaf213-73de-4416-b471-585de9cf1313
-- title:
--   Digit Bound: num Of E top
-- statement:
--   The Digit Bound construction uses the num Of E top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L342-L342
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L342-L342

import Definitions.Def_Fpy_DigitBound_Defs
import Definitions.Def_Fpy_DigitBound_Basic
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.numOfE_top : numOfE ⊤ = .special (.inf false) := by sorry

attribute [defeq] Fpy.DigitBound.numOfE_top
