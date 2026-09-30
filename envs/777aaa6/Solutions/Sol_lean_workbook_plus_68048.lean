-- Prove2me | solution 1 for lean_workbook_plus_68048
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:48:59.979682+00:00
-- url     : https://prove2.me/submissions/a9571dec-38ec-4f6f-9cb7-77cc14b1a9c6

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

theorem solution (a b c : ℝ) :
    (b ^ 4 * a ^ 2 + b ^ 2 * c ^ 4 + c ^ 2 * a ^ 4) ≥
      (b ^ 3 * c ^ 2 * a + c ^ 3 * a ^ 2 * b + a ^ 3 * b ^ 2 * c) := by
  nlinarith [sq_nonneg (a * b ^ 2 - b * c ^ 2),
    sq_nonneg (b * c ^ 2 - c * a ^ 2), sq_nonneg (c * a ^ 2 - a * b ^ 2)]

#print axioms solution
