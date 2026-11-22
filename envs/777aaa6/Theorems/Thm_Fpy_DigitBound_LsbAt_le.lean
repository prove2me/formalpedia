-- Prove2me | Theorems.Thm_Fpy_DigitBound_LsbAt_le
-- name    : Fpy.DigitBound.LsbAt.le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:17:18.473868+00:00
-- url     : https://prove2.me/theorems/a26c3c91-11f2-4f51-b647-8c6daed928ee
-- title:
--   Lsb At: le
-- statement:
--   The Lsb At construction uses the le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L57-L63
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L57-L63

import Definitions.Def_Fpy_DigitBound_Basic
import Definitions.Def_Fpy_DigitBound_Digits
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.LsbAt.le {x : ℝ} {j k : ℤ} (hj : LsbAt x j) (hk : LsbAt x k) : j ≤ k := by sorry
