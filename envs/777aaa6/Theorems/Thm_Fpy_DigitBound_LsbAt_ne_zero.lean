-- Prove2me | Theorems.Thm_Fpy_DigitBound_LsbAt_ne_zero
-- name    : Fpy.DigitBound.LsbAt.ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:22:26.458657+00:00
-- url     : https://prove2.me/theorems/7e910db1-d645-4096-b825-113806a03d50
-- title:
--   Lsb At: ne zero
-- statement:
--   The Lsb At construction uses the ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L52-L55
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L52-L55

import Definitions.Def_Fpy_DigitBound_Basic
import Definitions.Def_Fpy_DigitBound_Digits
import Theorems.Thm_Mpfx_Dyadic_IsRepresentableAtP_ne_zero
import Theorems.Thm_Mpfx_FiniteFormat_IsOdd_ne_zero

set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.LsbAt.ne_zero {x : ℝ} {k : ℤ} : LsbAt x k → x ≠ 0 := by sorry
