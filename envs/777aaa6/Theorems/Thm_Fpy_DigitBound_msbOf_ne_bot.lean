-- Prove2me | Theorems.Thm_Fpy_DigitBound_msbOf_ne_bot
-- name    : Fpy.DigitBound.msbOf_ne_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:22:52.610032+00:00
-- url     : https://prove2.me/theorems/94e2d469-908a-4744-b542-f49e604b293b
-- title:
--   Digit Bound: msb Of ne bot
-- statement:
--   The Digit Bound construction uses the msb Of ne bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L133-L134
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Digits.lean#L133-L134

import Definitions.Def_Fpy_DigitBound_Basic
import Definitions.Def_Fpy_DigitBound_Digits
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.msbOf_ne_bot {x : ℝ} (h0 : x ≠ 0) : msbOf (.finite x) ≠ ⊥ := by sorry
