-- Prove2me | solution 2 for fermat_last_theorem
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-15T06:35:10.506473+00:00
-- url     : https://prove2.me/submissions/8f6c10c7-d002-4b04-ac3d-720a050d3fd3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Theorems.Thm_flt_n_eq_4
import Theorems.Thm_flt_n_odd_prime
import Theorems.Thm_flt_reduction

theorem solution
    (n : ℕ) (hn : 3 ≤ n)
    (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ n + b ^ n ≠ c ^ n :=
  flt_reduction flt_n_eq_4 flt_n_odd_prime n hn a b c ha hb hc
