-- Prove2me | solution 1 for lean_workbook_plus_79950
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:15:27.640404+00:00
-- url     : https://prove2.me/submissions/19c00b3a-e626-4016-b805-1e30b44d737b

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

theorem solution : ∀ x y : ℝ,
    12 * (x ^ 3 + 14 * x ^ 2 - 2 * x - (y ^ 3 + 14 * y ^ 2 - 2 * y)) =
      (x - y) * (3 * (2 * x + y + 14) ^ 2 + (3 * y + 14) ^ 2 - 808) := by
  intro x y
  ring

#print axioms solution
