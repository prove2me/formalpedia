-- Prove2me | solution 1 for flt5_case1_sum_is_fifth_power
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-12T09:08:58.470444+00:00
-- url     : https://prove2.me/submissions/fa8bf5d4-0bab-4ade-99e3-d035e094be1b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_flt5_case1_sum_is_fifth_power
import Theorems.Thm_coprime_fifth_power_factor
import Theorems.Thm_flt5_descent_gcd_one
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Ring

theorem solution : flt5_case1_sum_is_fifth_power := by
  intro a b c h_eq h_cop h_not5c
  -- Step 1: ring identity gives (a+b)·Phi10(a,b) = c^5
  have hfact : (a + b) * (a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4) = c ^ 5 :=
    calc (a + b) * (a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4)
        = a ^ 5 + b ^ 5 := by ring
      _ = c ^ 5 := h_eq
  -- Step 2: gcd(a+b, Phi10) = 1 from flt5_descent_gcd_one
  have hgcd : Int.gcd (a + b) (a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4) = 1 :=
    flt5_descent_gcd_one a b c h_eq h_cop h_not5c
  -- Step 3: coprime factor theorem gives a+b is a 5th power
  exact coprime_fifth_power_factor (a + b)
    (a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4) c hgcd hfact
