-- Prove2me | solution 2 for selmer_group_control
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T19:32:35.728581+00:00
-- url     : https://prove2.me/submissions/82ada0d0-9314-4b38-a6ac-1556c41c31d0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic
import Theorems.Thm_iwasawa_freeness

theorem solution (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : Nat.Coprime a b) (hbc : Nat.Coprime b c) (hac : Nat.Coprime a c) (heq : a ^ p + b ^ p = c ^ p) :
    False :=
  iwasawa_freeness p hp h5 a b c ha hb hc hab hbc hac heq
