-- Prove2me | Theorems.Thm_Fpy_DigitBound_EInt_top_add
-- name    : Fpy.DigitBound.EInt.top_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:18:29.450404+00:00
-- url     : https://prove2.me/theorems/9d0cc458-f619-4b60-a36c-d2c108b323bc
-- title:
--   EInt: top add
-- statement:
--   The EInt construction uses the top add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L139-L143
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L139-L143

import Definitions.Def_Fpy_DigitBound_Basic
import Definitions.Def_Fpy_DigitBound_Digits
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.EInt.top_add {a : EInt} (h : a ≠ ⊥) : ⊤ + a = ⊤ := by sorry
