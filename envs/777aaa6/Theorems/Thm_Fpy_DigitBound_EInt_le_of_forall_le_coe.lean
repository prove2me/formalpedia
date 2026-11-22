-- Prove2me | Theorems.Thm_Fpy_DigitBound_EInt_le_of_forall_le_coe
-- name    : Fpy.DigitBound.EInt.le_of_forall_le_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:20:16.759376+00:00
-- url     : https://prove2.me/theorems/7c1c6157-8bbb-4eb5-8d96-eb72d0b7e718
-- title:
--   EInt: le of forall le coe
-- statement:
--   `a ≤ b` once every integer above `b` is above `a`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L32-L40
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L32-L40

import Definitions.Def_Fpy_DigitBound_Basic
import Definitions.Def_Fpy_DigitBound_Digits
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.EInt.le_of_forall_le_coe {a b : EInt} (h : ∀ k : ℤ, b ≤ k → a ≤ k) : a ≤ b := by sorry
