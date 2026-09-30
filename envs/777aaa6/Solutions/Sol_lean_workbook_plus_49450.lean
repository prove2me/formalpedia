-- Prove2me | solution 1 for lean_workbook_plus_49450
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:01:10.870823+00:00
-- url     : https://prove2.me/submissions/9c5c3237-77af-4892-99e1-5c4a2f311ca6

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem sixth_power_identity (x y : ℝ) :
    x ^ 6 + y ^ 6 = (x + y) ^ 6 - 6 * (x * y) * (x + y) ^ 4 +
      9 * (x * y) ^ 2 * (x + y) ^ 2 - 2 * (x * y) ^ 3 := by ring

theorem solution (x y : ℝ) (h₁ : x + y = 4) (h₂ : x * y = 2) :
    x ^ 6 + y ^ 6 = 1584 := by
  rw [sixth_power_identity, h₁, h₂]
  norm_num

#print axioms solution
#print axioms sixth_power_identity
