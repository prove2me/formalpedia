-- Prove2me | Theorems.Thm_ZMod_snd_comp_chineseRemainder
-- name    : ZMod.snd_comp_chineseRemainder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:13:28.898831+00:00
-- url     : https://prove2.me/theorems/a551df49-4fd1-45ea-beab-88a19beea9a5
-- title:
--   ZMod: snd comp chinese Remainder
-- statement:
--   The ZMod construction uses the snd comp chinese Remainder property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Mathlib/Data/ZMod/Basic.lean#L21-L24
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Mathlib/Data/ZMod/Basic.lean#L21-L24

import Mathlib.Data.ZMod.Basic
import Definitions.Def_MillerRabin_Mathlib_Data_ZMod_Basic
set_option autoImplicit false
open ZMod

theorem ZMod.snd_comp_chineseRemainder {m n : ℕ} (h : m.Coprime n) :
    (RingHom.snd (ZMod m) (ZMod n)).comp (ZMod.chineseRemainder h) =
      ZMod.castHom (dvd_mul_left n m) (ZMod n) := by sorry
