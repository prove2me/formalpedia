-- Prove2me | solution 1 for lean_workbook_plus_21442
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:45:45.700498+00:00
-- url     : https://prove2.me/submissions/ce5c68d8-bcb9-41c2-969b-f73eb32ca968

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) (h : a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b * c = 1) :
  (a + b + c) ^ 2 ≥ 3 * (a * b + b * c + c * a) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
