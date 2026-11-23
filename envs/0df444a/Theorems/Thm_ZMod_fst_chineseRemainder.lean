-- Prove2me | Theorems.Thm_ZMod_fst_chineseRemainder
-- name    : ZMod.fst_chineseRemainder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:10:30.392205+00:00
-- url     : https://prove2.me/theorems/9c9acce7-5785-4bcd-bce1-8fd015091a33
-- title:
--   ZMod: fst chinese Remainder
-- statement:
--   The ZMod construction uses the fst chinese Remainder property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Mathlib/Data/ZMod/Basic.lean#L7-L9
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Mathlib/Data/ZMod/Basic.lean#L7-L9

import Mathlib.Data.ZMod.Basic
import Definitions.Def_MillerRabin_Mathlib_Data_ZMod_Basic
set_option autoImplicit false
open ZMod

theorem ZMod.fst_chineseRemainder {m n : ℕ} {x : ZMod (m * n)} (h : m.Coprime n) :
    (ZMod.chineseRemainder h x).1 = x.cast := by sorry
