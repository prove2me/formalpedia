-- Prove2me | Theorems.Thm_Fpy_DigitBound_Num_add_nan_left
-- name    : Fpy.DigitBound.Num.add_nan_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:44:35.057868+00:00
-- url     : https://prove2.me/theorems/32ecbe95-5204-4ab3-ba9d-b548d200a4a4
-- title:
--   Num: add nan left
-- statement:
--   The Num construction uses the add nan left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Sum.lean#L21-L22
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Sum.lean#L21-L22

import Definitions.Def_Fpy_DigitBound_Sound
import Definitions.Def_Fpy_Sum
import Definitions.Def_Fpy_DigitBound_Sum
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.Num.add_nan_left (w : Num) : Num.add nan w = nan := by sorry
