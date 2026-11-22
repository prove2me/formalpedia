-- Prove2me | Theorems.Thm_Fpy_DigitBound_coe_le_lsbOf
-- name    : Fpy.DigitBound.coe_le_lsbOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:17:21.084818+00:00
-- url     : https://prove2.me/theorems/de551e85-17fa-4da5-bf78-3d3246959d03
-- title:
--   Digit Bound: coe le lsb Of
-- statement:
--   The Digit Bound construction uses the coe le lsb Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L88-L101
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L88-L101

import Definitions.Def_Fpy_DigitBound_Basic
import Definitions.Def_Fpy_DigitBound_Digits
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.coe_le_lsbOf {x : ℝ} {k : ℤ} : (k : EInt) ≤ lsbOf (.finite x) ↔ ∃ z : ℤ, x = z * 2 ^ k := by sorry
