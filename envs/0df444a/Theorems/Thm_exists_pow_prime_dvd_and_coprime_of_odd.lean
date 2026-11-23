-- Prove2me | Theorems.Thm_exists_pow_prime_dvd_and_coprime_of_odd
-- name    : exists_pow_prime_dvd_and_coprime_of_odd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:10:38.659857+00:00
-- url     : https://prove2.me/theorems/03a5c62a-b7f8-4399-ad1f-f818f5673c34
-- title:
--   exists pow prime dvd and coprime of odd: exists pow prime dvd and coprime of odd
-- statement:
--   This is too specific to put in mathlib
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Lemmas.lean#L50-L62
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Lemmas.lean#L50-L62

import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Ring.Regular
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.ZMod.Units
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.Field.Power
import Definitions.Def_MillerRabin_Lemmas
set_option autoImplicit false
open Nat

theorem exists_pow_prime_dvd_and_coprime_of_odd {n : ℕ} (hn : 2 ≤ n) (ho : Odd n) (hnp : ¬IsPrimePow n) :
    ∃ p s k : ℕ, p.Prime ∧ 0 < s ∧ n = p ^ s * k ∧ (p ^ s).Coprime k ∧ 2 < k ∧ 2 < p ^ s := by sorry
