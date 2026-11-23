-- Prove2me | Theorems.Thm_randNat_le_lo_of_ge
-- name    : randNat_le_lo_of_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:15:01.202141+00:00
-- url     : https://prove2.me/theorems/6f3bf1bd-dcef-4e6e-8d43-cbab4401e591
-- title:
--   rand Nat le lo of ge: rand Nat le lo of ge
-- statement:
--   The rand Nat le lo of ge construction uses the rand Nat le lo of ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/MillerRabin.lean#L25-L32
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/MillerRabin.lean#L25-L32

import Definitions.Def_MillerRabin_StrongProbable
import Definitions.Def_MillerRabin_MillerRabin
set_option autoImplicit false

theorem randNat_le_lo_of_ge {gen : Type _} [RandomGen gen] (g : gen) (lo hi : Nat) (h : lo ≥ hi) :
    (randNat g lo hi).1 ≤ lo := by sorry
