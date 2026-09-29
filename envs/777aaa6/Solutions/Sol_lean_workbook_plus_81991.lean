-- Prove2me | solution 1 for lean_workbook_plus_81991
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-17T14:28:17.91909+00:00
-- url     : https://prove2.me/submissions/9ee7376f-0e6a-4062-bd4e-394a438c63d4

import Mathlib.Tactic

theorem solution (a b c : ℝ) : (a ^ 2 + b ^ 2 + c ^ 2 + 3) / 2 ≥ a + b + c := by
  nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]
