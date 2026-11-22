-- Prove2me | Theorems.Thm_Fpy_DigitBound_coe_min_coe
-- name    : Fpy.DigitBound.coe_min_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:21:09.718771+00:00
-- url     : https://prove2.me/theorems/aa53065c-24f8-4fb2-aedb-8b20d405126f
-- title:
--   Digit Bound: coe min coe
-- statement:
--   The Digit Bound construction uses the coe min coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L353-L354
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L353-L354

import Definitions.Def_Fpy_DigitBound_Defs
import Definitions.Def_Fpy_DigitBound_Basic
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.coe_min_coe (a b : ℤ) : min (a : EInt) (b : EInt) = ((min a b : ℤ) : EInt) := by sorry
