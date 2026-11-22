-- Prove2me | Theorems.Thm_Fpy_DigitBound_lsbOf_ne_top
-- name    : Fpy.DigitBound.lsbOf_ne_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:19:16.855703+00:00
-- url     : https://prove2.me/theorems/b7d9bfdc-b648-4e7f-af42-2398ac49bd1a
-- title:
--   Digit Bound: lsb Of ne top
-- statement:
--   The Digit Bound construction uses the lsb Of ne top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L84-L86
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L84-L86

import Definitions.Def_Fpy_DigitBound_Basic
import Definitions.Def_Fpy_DigitBound_Digits
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.lsbOf_ne_top {x : ℝ} (h0 : x ≠ 0) : lsbOf (.finite x) ≠ ⊤ := by sorry
