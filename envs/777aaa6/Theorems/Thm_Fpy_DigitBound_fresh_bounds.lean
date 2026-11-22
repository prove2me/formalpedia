-- Prove2me | Theorems.Thm_Fpy_DigitBound_fresh_bounds
-- name    : Fpy.DigitBound.fresh_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:19:30.309941+00:00
-- url     : https://prove2.me/theorems/c5c21cbd-fcf6-494f-9ef0-5f343d9a766b
-- title:
--   Digit Bound: fresh bounds
-- statement:
--   The Digit Bound construction uses the fresh bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L299-L303
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L299-L303

import Definitions.Def_Fpy_DigitBound_Defs
import Definitions.Def_Fpy_DigitBound_Basic
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.fresh_bounds (n : ℕ) {Lo Hi : Term} (hLo : Lo.Below (n + 1)) (hHi : Hi.Below n) :
    Fresh n (n + 2) (bounds n Lo Hi hLo hHi) := by sorry
