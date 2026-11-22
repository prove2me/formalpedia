-- Prove2me | Theorems.Thm_Fpy_DigitBound_logb_eq
-- name    : Fpy.DigitBound.logb_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:21:17.241268+00:00
-- url     : https://prove2.me/theorems/a1c0d499-feaa-4740-89a9-0598d00e7d32
-- title:
--   Digit Bound: logb eq
-- statement:
--   The Digit Bound construction uses the logb eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L373-L378
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L373-L378

import Definitions.Def_Fpy_DigitBound_Defs
import Definitions.Def_Fpy_DigitBound_Basic
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.logb_eq {u : Num} (hu : u ≠ nan) : Num.logb u = numOfE (msbOf u) := by sorry
