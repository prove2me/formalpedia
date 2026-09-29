-- Prove2me | solution 1 for flt_n_odd_prime
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-11T08:31:03.684639+00:00
-- url     : https://prove2.me/submissions/8e02acdd-8dd2-40b1-b736-4f6084af4415
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_flt_n_odd_prime
import Theorems.Thm_flt_three
import Theorems.Thm_flt_odd_prime_ge_5
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic

theorem solution
    (p : ℕ) (hp : p.Prime) (hodd : 2 < p)
    (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ p + b ^ p ≠ c ^ p := by
  by_cases h3 : p = 3
  · subst h3; exact flt_three a b c ha hb hc
  · have h5 : 5 ≤ p := by
      have hge3 : 3 ≤ p := by have := hp.two_le; omega
      by_cases hlt : 5 ≤ p
      · exact hlt
      · have hp4 : p = 4 := by omega
        exact absurd hp (hp4 ▸ by decide)
    exact flt_odd_prime_ge_5 p hp h5 a b c ha hb hc
