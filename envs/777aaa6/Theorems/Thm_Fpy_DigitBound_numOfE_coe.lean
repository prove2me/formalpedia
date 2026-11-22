-- Prove2me | Theorems.Thm_Fpy_DigitBound_numOfE_coe
-- name    : Fpy.DigitBound.numOfE_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:16:13.913667+00:00
-- url     : https://prove2.me/theorems/5364a4c6-4bae-46a7-9acd-02fb5467f02d
-- title:
--   Digit Bound: num Of E coe
-- statement:
--   The Digit Bound construction uses the num Of E coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L343-L343
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L343-L343

import Definitions.Def_Fpy_DigitBound_Defs
import Definitions.Def_Fpy_DigitBound_Basic
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.numOfE_coe (k : ℤ) : numOfE k = .finite (k : ℝ) := by sorry

attribute [defeq] Fpy.DigitBound.numOfE_coe
