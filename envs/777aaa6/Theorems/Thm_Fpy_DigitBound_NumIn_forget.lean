-- Prove2me | Theorems.Thm_Fpy_DigitBound_NumIn_forget
-- name    : Fpy.DigitBound.NumIn.forget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:21:30.788177+00:00
-- url     : https://prove2.me/theorems/a40bbda9-02e4-467d-a717-c1b6f8fa108a
-- title:
--   Num In: forget
-- statement:
--   The Num In construction uses the forget property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L389-L391
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L389-L391

import Definitions.Def_Fpy_DigitBound_Defs
import Definitions.Def_Fpy_DigitBound_Basic
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.NumIn.forget {ι : Asgn} {l m : Term} {τ : Option Term} {u : Num} (h : NumIn ι l m τ u) :
    NumIn ι l m none u := by sorry
