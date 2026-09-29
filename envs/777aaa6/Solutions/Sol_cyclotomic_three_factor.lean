-- Prove2me | solution 1 for cyclotomic_three_factor
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-12T05:41:07.876027+00:00
-- url     : https://prove2.me/submissions/d82aa914-cece-4232-985d-e47e7c6cfe10

import Theorems.Thm_cyclotomic_three_factor
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring

theorem solution (a b : ℤ) : a ^ 3 + b ^ 3 = (a + b) * (a ^ 2 - a * b + b ^ 2) := by
  ring
