-- Prove2me | Theorems.Thm_Fpy_DigitBound_EInt_add_top
-- name    : Fpy.DigitBound.EInt.add_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:19:18.992215+00:00
-- url     : https://prove2.me/theorems/d64429d9-9d8e-4611-a1d2-671660aee4c3
-- title:
--   EInt: add top
-- statement:
--   The EInt construction uses the add top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L145-L146
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L145-L146

import Definitions.Def_Fpy_DigitBound_Basic
import Definitions.Def_Fpy_DigitBound_Digits
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.EInt.add_top {a : EInt} (h : a ≠ ⊥) : a + ⊤ = ⊤ := by sorry
