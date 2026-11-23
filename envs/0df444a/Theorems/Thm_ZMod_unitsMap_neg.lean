-- Prove2me | Theorems.Thm_ZMod_unitsMap_neg
-- name    : ZMod.unitsMap_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:11:44.991786+00:00
-- url     : https://prove2.me/theorems/6888506a-13e5-4ebb-9a66-de973ae5131f
-- title:
--   ZMod: units Map neg
-- statement:
--   The ZMod construction uses the units Map neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Mathlib/Data/ZMod/Units.lean#L48-L50
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Mathlib/Data/ZMod/Units.lean#L48-L50

import Mathlib.Data.ZMod.Units
import Definitions.Def_MillerRabin_Mathlib_Data_ZMod_Basic
import Definitions.Def_MillerRabin_Mathlib_Data_ZMod_Units
set_option autoImplicit false
open ZMod

theorem ZMod.unitsMap_neg {n m : ℕ} (hm : n ∣ m) (x : (ZMod m)ˣ) :
    unitsMap hm (-x) = -unitsMap hm x := by sorry
