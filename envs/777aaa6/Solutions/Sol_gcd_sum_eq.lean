-- Prove2me | solution 1 for gcd_sum_eq
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-12T06:14:41.563533+00:00
-- url     : https://prove2.me/submissions/2901e558-82e6-42ef-86de-fb4251425a30

import Theorems.Thm_gcd_sum_eq
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Ring

theorem solution (a b : ℤ) : Int.gcd (a + b) a = Int.gcd b a := by
  rw [Int.gcd_comm (a + b) a]
  -- goal: a.gcd (a + b) = b.gcd a
  have h := @Int.gcd_add_mul_right_right a b 1
  simp only [one_mul] at h
  -- h : a.gcd (b + a) = a.gcd b
  rw [show a + b = b + a from by ring, h, Int.gcd_comm]
