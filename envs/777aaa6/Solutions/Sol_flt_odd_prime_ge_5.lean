-- Prove2me | solution 1 for flt_odd_prime_ge_5
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-11T08:34:26.541169+00:00
-- url     : https://prove2.me/submissions/338ff9e4-8dc8-4701-a349-a74b5ccdc53e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_flt_odd_prime_ge_5
import Theorems.Thm_flt_odd_prime_coprime_reduction
import Theorems.Thm_flt_wiles_coprime_case
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic

theorem solution
    (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p)
    (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ p + b ^ p ≠ c ^ p :=
  flt_odd_prime_coprime_reduction p hp h5 a b c ha hb hc
    (fun a' b' c' ha' hb' hc' hab' hbc' hac' =>
      flt_wiles_coprime_case p hp h5 a' b' c' ha' hb' hc' hab' hbc' hac')
