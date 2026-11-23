-- Prove2me | Theorems.Thm_exists_pow_prime_dvd_and_coprime
-- name    : exists_pow_prime_dvd_and_coprime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:12:55.612558+00:00
-- url     : https://prove2.me/theorems/95dc8e50-7d3b-49bc-80dd-2b2e591bdb84
-- title:
--   exists pow prime dvd and coprime: exists pow prime dvd and coprime
-- statement:
--   This one is not used and is too specific to put in mathlib
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Lemmas.lean#L37-L47
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Lemmas.lean#L37-L47

import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Ring.Regular
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.ZMod.Units
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.Field.Power
import Definitions.Def_MillerRabin_Lemmas
set_option autoImplicit false
open Nat

theorem exists_pow_prime_dvd_and_coprime {n : ℕ} (hn : 2 ≤ n) :
    ∃ p s k : ℕ, p.Prime ∧ 0 < s ∧ n = p ^ s * k ∧ (p ^ s).Coprime k := by sorry
