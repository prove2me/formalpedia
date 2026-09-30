-- Prove2me | solution 1 for lean_workbook_plus_74931
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:34:44.76257+00:00
-- url     : https://prove2.me/submissions/21c621e1-68b5-4999-8435-77248b44eb79

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≥
      3 * (a + b + c) * (b + c - a) * (a + c - b) * (a + b - c) := by
  nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (b ^ 2 - c ^ 2),
    sq_nonneg (c ^ 2 - a ^ 2)]

#print axioms solution
