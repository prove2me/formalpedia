-- Prove2me | solution 1 for lean_workbook_plus_77251
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:40:48.888202+00:00
-- url     : https://prove2.me/submissions/0875ddb0-52a1-4413-aa44-93b8a0e1e48a

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b c : ℝ) :
    3 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 + 6 * (a * b + b * c + c * a) ^ 2 ≥
      (a + b + c) ^ 4 := by
  nlinarith [sq_nonneg (a ^ 2 + b ^ 2 + c ^ 2 - (a * b + b * c + c * a))]

#print axioms solution
