-- Prove2me | solution 2 for flt_odd_prime_ge_5
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-15T06:31:26.789872+00:00
-- url     : https://prove2.me/submissions/c3daace5-c09b-4c25-9ede-73d462dd3a65
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Theorems.Thm_flt_five
import Theorems.Thm_flt_odd_prime_gt_5

theorem solution (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p)
    (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ p + b ^ p ≠ c ^ p := by
  by_cases hp5 : p = 5
  · subst hp5; exact flt_five a b c ha hb hc
  · have h7 : 7 ≤ p := by
      have h6 : 6 ≤ p := by omega
      have hp6 : p ≠ 6 := fun h => absurd (h ▸ hp) (by decide)
      omega
    exact flt_odd_prime_gt_5 p hp h7 a b c ha hb hc
