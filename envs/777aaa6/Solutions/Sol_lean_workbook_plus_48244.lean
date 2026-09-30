-- Prove2me | solution 1 for lean_workbook_plus_48244
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:12:58.233418+00:00
-- url     : https://prove2.me/submissions/e2141039-c773-46df-8e04-d3ebbbc5539d

import Mathlib
set_option autoImplicit false

theorem solution (a b c d : ℝ) : 4 * (a * b + b * c + c * d + d * a) ≤ (a + b + c + d) ^ 2   := by
  have := sq_nonneg (a - b + c - d)
  linarith

#print axioms solution
