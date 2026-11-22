-- Prove2me | Theorems.Thm_Fpy_DigitBound_EInt_add_coe_le_coe
-- name    : Fpy.DigitBound.EInt.add_coe_le_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:22:10.968852+00:00
-- url     : https://prove2.me/theorems/db7b0d45-2e27-460c-9b73-2fcf284f2258
-- title:
--   EInt: add coe le coe
-- statement:
--   The EInt construction uses the add coe le coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L44-L48
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L44-L48

import Definitions.Def_Fpy_DigitBound_Basic
import Definitions.Def_Fpy_DigitBound_Digits
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.EInt.add_coe_le_coe {a : EInt} {j k : ℤ} : a + j ≤ k ↔ a ≤ ((k - j : ℤ) : EInt) := by sorry
