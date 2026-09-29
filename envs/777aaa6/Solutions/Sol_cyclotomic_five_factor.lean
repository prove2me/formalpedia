-- Prove2me | solution 1 for cyclotomic_five_factor
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-12T05:37:43.109926+00:00
-- url     : https://prove2.me/submissions/c88ce311-e3c3-4b46-95d7-4cab0d124024

import Theorems.Thm_cyclotomic_five_factor
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring

theorem solution (a b : ℤ) : a ^ 5 + b ^ 5 = (a + b) * (a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4) := by
  ring
