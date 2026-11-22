-- Prove2me | Theorems.Thm_Fpy_DigitBound_Num_add_nan_right
-- name    : Fpy.DigitBound.Num.add_nan_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:44:54.075904+00:00
-- url     : https://prove2.me/theorems/f0436ffb-590c-44a8-9671-ee7ce32d1a5c
-- title:
--   Num: add nan right
-- statement:
--   The Num construction uses the add nan right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Sum.lean#L24-L25
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Sum.lean#L24-L25

import Definitions.Def_Fpy_DigitBound_Sound
import Definitions.Def_Fpy_Sum
import Definitions.Def_Fpy_DigitBound_Sum
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.Num.add_nan_right (s : Num) : Num.add s nan = nan := by sorry
