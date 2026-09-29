-- Prove2me | solution 1 for flt5_descent_step
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-12T11:16:10.889026+00:00
-- url     : https://prove2.me/submissions/d977c85b-6115-4e8a-beaa-be2ae734bbfd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_flt5_descent_step
import Theorems.Thm_flt5_pow4_dvd_sum
import Theorems.Thm_flt5_descent_from_pow4
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD

-- Sketch: split descent_step into:
--   (a) 5^4 | a+b   (provable via LTE)
--   (b) from 5^4 | a+b, produce the smaller solution (hard, left open)

theorem solution (a b c : ℤ) (h_eq : a ^ 5 + b ^ 5 = c ^ 5)
    (h_cop : Int.gcd a b = 1) (h5c : (5 : ℤ) ∣ c) (hc : c ≠ 0) :
    ∃ a' b' c' : ℤ, a' ^ 5 + b' ^ 5 = c' ^ 5 ∧ Int.gcd a' b' = 1 ∧
    (5 : ℤ) ∣ c' ∧ c' ≠ 0 ∧ c'.natAbs < c.natAbs := by
  have h54 : (5 : ℤ) ^ 4 ∣ a + b := flt5_pow4_dvd_sum a b c h_eq h_cop h5c hc
  exact flt5_descent_from_pow4 a b c h_eq h_cop h5c hc h54
