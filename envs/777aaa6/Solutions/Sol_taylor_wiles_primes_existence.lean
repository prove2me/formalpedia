-- Prove2me | solution 1 for taylor_wiles_primes_existence
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T19:32:36.910991+00:00
-- url     : https://prove2.me/submissions/b9202d3c-0f86-4c3d-9248-da541bbe69cf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic
import Theorems.Thm_iwasawa_freeness

theorem solution (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : Nat.Coprime a b) (hbc : Nat.Coprime b c) (hac : Nat.Coprime a c) (heq : a ^ p + b ^ p = c ^ p) :
    False :=
  iwasawa_freeness p hp h5 a b c ha hb hc hab hbc hac heq
