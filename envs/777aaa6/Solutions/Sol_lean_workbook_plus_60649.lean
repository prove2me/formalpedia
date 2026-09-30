-- Prove2me | solution 1 for lean_workbook_plus_60649
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:52:44.802962+00:00
-- url     : https://prove2.me/submissions/9cfe9427-3bf7-4f91-a045-3e88fc36b0c8

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (x y : ℂ) : ‖x * y‖ ≤ (1 / 2) * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  rw [norm_mul]
  nlinarith only [sq_nonneg (‖x‖ - ‖y‖)]

#print axioms solution
