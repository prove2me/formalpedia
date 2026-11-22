-- Prove2me | Theorems.Thm_Fpy_DigitBound_EInt_le_of_forall_coe_le
-- name    : Fpy.DigitBound.EInt.le_of_forall_coe_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:17:59.234459+00:00
-- url     : https://prove2.me/theorems/00ddcc6b-4d54-45fc-ad2b-5a083d42de8d
-- title:
--   EInt: le of forall coe le
-- statement:
--   `a ≤ b` once every integer below `a` is below `b`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L20-L29
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L20-L29

import Definitions.Def_Fpy_DigitBound_Basic
import Definitions.Def_Fpy_DigitBound_Digits
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.EInt.le_of_forall_coe_le {a b : EInt} (h : ∀ k : ℤ, (k : EInt) ≤ a → (k : EInt) ≤ b) :
    a ≤ b := by sorry
