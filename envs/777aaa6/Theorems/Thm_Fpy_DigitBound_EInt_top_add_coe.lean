-- Prove2me | Theorems.Thm_Fpy_DigitBound_EInt_top_add_coe
-- name    : Fpy.DigitBound.EInt.top_add_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:17:08.995611+00:00
-- url     : https://prove2.me/theorems/6ea04d62-1107-4364-a9dc-594232967cfe
-- title:
--   EInt: top add coe
-- statement:
--   The EInt construction uses the top add coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L42-L42
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L42-L42

import Definitions.Def_Fpy_DigitBound_Basic
import Definitions.Def_Fpy_DigitBound_Digits
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.EInt.top_add_coe (k : ℤ) : (⊤ : EInt) + k = ⊤ := by sorry

attribute [defeq] Fpy.DigitBound.EInt.top_add_coe
