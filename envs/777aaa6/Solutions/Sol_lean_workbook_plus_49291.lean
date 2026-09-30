-- Prove2me | solution 1 for lean_workbook_plus_49291
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:45:32.700278+00:00
-- url     : https://prove2.me/submissions/48c6245b-c756-4ac7-87b3-b12758ef8792

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a x y : ℝ) (ha : a = x + y) (hb : a ^ 2 - 1 = 4 * x * y) :
    a - Real.sqrt (a ^ 2 - 1) = x + y - 2 * Real.sqrt (x * y) := by
  rw [hb, mul_assoc, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num [ha]

#print axioms solution
