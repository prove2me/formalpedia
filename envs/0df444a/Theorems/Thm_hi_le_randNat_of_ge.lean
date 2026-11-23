-- Prove2me | Theorems.Thm_hi_le_randNat_of_ge
-- name    : hi_le_randNat_of_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:13:56.650217+00:00
-- url     : https://prove2.me/theorems/8abbff9b-4962-4e82-928d-bbfbc4d75d3f
-- title:
--   hi le rand Nat of ge: hi le rand Nat of ge
-- statement:
--   The hi le rand Nat of ge construction uses the hi le rand Nat of ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/MillerRabin.lean#L19-L23
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/MillerRabin.lean#L19-L23

import Definitions.Def_MillerRabin_StrongProbable
import Definitions.Def_MillerRabin_MillerRabin
set_option autoImplicit false

theorem hi_le_randNat_of_ge {gen : Type _} [RandomGen gen] (g : gen) (lo hi : Nat) (h : lo ≥ hi) :
    hi ≤ (randNat g lo hi).1 := by sorry
