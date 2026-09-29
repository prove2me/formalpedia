-- Prove2me | solution 1 for cyclotomic_seven_factor
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-12T05:41:08.284664+00:00
-- url     : https://prove2.me/submissions/cf9477b2-de4d-45df-b5c0-9fe54d601802

import Theorems.Thm_cyclotomic_seven_factor
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring

theorem solution (a b : ℤ) : a ^ 7 + b ^ 7 = (a + b) * (a ^ 6 - a ^ 5 * b + a ^ 4 * b ^ 2 - a ^ 3 * b ^ 3 + a ^ 2 * b ^ 4 - a * b ^ 5 + b ^ 6) := by
  ring
