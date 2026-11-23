-- Prove2me | Theorems.Thm_ZMod_snd_chineseRemainder
-- name    : ZMod.snd_chineseRemainder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:10:27.567903+00:00
-- url     : https://prove2.me/theorems/2adc5990-acca-4309-a37a-c824c4e7e508
-- title:
--   ZMod: snd chinese Remainder
-- statement:
--   The ZMod construction uses the snd chinese Remainder property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Mathlib/Data/ZMod/Basic.lean#L17-L19
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Mathlib/Data/ZMod/Basic.lean#L17-L19

import Mathlib.Data.ZMod.Basic
import Definitions.Def_MillerRabin_Mathlib_Data_ZMod_Basic
set_option autoImplicit false
open ZMod

theorem ZMod.snd_chineseRemainder {m n : ℕ} {x : ZMod (m * n)} (h : m.Coprime n) :
    (ZMod.chineseRemainder h x).2 = x.cast := by sorry
