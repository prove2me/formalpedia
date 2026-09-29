-- Prove2me | solution 4 for flt5_descent_step
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-12T18:13:09.185247+00:00
-- url     : https://prove2.me/submissions/f1a34230-cb75-4d11-ba79-1e06d6ee16f5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_flt5_pow4_dvd_sum
import Theorems.Thm_flt5_descent_from_pow4
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD

-- Sketch: flt5_descent_step
-- Main descent step: from a^5+b^5=c^5, coprime, 5|c → smaller coprime solution.
-- Children:
--   flt5_pow4_dvd_sum (PROVED): 5^4 | a+b (via lifting-the-exponent)
--   flt5_descent_from_pow4 (OPEN): from 5^4 | a+b, produce smaller solution

theorem solution (a b c : ℤ) (h_eq : a ^ 5 + b ^ 5 = c ^ 5)
    (h_cop : Int.gcd a b = 1) (h5c : (5 : ℤ) ∣ c) (hc : c ≠ 0) :
    ∃ a' b' c' : ℤ, a' ^ 5 + b' ^ 5 = c' ^ 5 ∧ Int.gcd a' b' = 1 ∧
    (5 : ℤ) ∣ c' ∧ c' ≠ 0 ∧ c'.natAbs < c.natAbs := by
  have h54 : (5 : ℤ) ^ 4 ∣ a + b := flt5_pow4_dvd_sum a b c h_eq h_cop h5c hc
  exact flt5_descent_from_pow4 a b c h_eq h_cop h5c hc h54
