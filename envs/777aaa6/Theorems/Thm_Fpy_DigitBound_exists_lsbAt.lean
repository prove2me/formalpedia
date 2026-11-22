-- Prove2me | Theorems.Thm_Fpy_DigitBound_exists_lsbAt
-- name    : Fpy.DigitBound.exists_lsbAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:22:16.125184+00:00
-- url     : https://prove2.me/theorems/58e850be-cda8-4ba1-83c6-b74009214614
-- title:
--   Digit Bound: exists lsb At
-- statement:
--   A nonzero multiple of `2ᵏ` has its least significant digit at or above `k`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L72-L82
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L72-L82

import Definitions.Def_Fpy_DigitBound_Basic
import Definitions.Def_Fpy_DigitBound_Digits
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.exists_lsbAt {x : ℝ} {z k : ℤ} (hx : x = z * 2 ^ k) (h0 : x ≠ 0) :
    ∃ j, k ≤ j ∧ LsbAt x j := by sorry
