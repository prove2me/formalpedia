-- Prove2me | Theorems.Thm_ZMod_add_mul_prime_pow_pow
-- name    : ZMod.add_mul_prime_pow_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:10:38.082862+00:00
-- url     : https://prove2.me/theorems/78c583ff-b5cb-4c71-89b4-2da3cc85b2af
-- title:
--   ZMod: add mul prime pow pow
-- statement:
--   The ZMod construction uses the add mul prime pow pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Lemmas.lean#L17-L32
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Lemmas.lean#L17-L32

import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Ring.Regular
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.ZMod.Units
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.Field.Power
import Definitions.Def_MillerRabin_Lemmas
set_option autoImplicit false
open Nat
open ZMod

theorem ZMod.add_mul_prime_pow_pow {p m n : ℕ} (x c : ZMod (p ^ (m + 1))) (hm : 0 < m) (hn : 0 < n) :
    (x + c * p ^ m) ^ n = x ^ n + x ^ (n - 1) * c * p ^ m * n := by sorry
