-- Prove2me | Theorems.Thm_ZMod_fst_comp_chineseRemainder
-- name    : ZMod.fst_comp_chineseRemainder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:13:32.223289+00:00
-- url     : https://prove2.me/theorems/b82c1ac0-d682-45eb-813c-899c981f8d65
-- title:
--   ZMod: fst comp chinese Remainder
-- statement:
--   The ZMod construction uses the fst comp chinese Remainder property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Mathlib/Data/ZMod/Basic.lean#L11-L14
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Mathlib/Data/ZMod/Basic.lean#L11-L14

import Mathlib.Data.ZMod.Basic
import Definitions.Def_MillerRabin_Mathlib_Data_ZMod_Basic
set_option autoImplicit false
open ZMod

theorem ZMod.fst_comp_chineseRemainder {m n : ℕ} (h : m.Coprime n) :
    (RingHom.fst (ZMod m) (ZMod n)).comp (ZMod.chineseRemainder h) =
      ZMod.castHom (dvd_mul_right m n) (ZMod m) := by sorry
