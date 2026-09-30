-- Prove2me | solution 1 for lean_workbook_plus_13848
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:42:23.4342+00:00
-- url     : https://prove2.me/submissions/cfcdef4e-3ede-4cfc-9df8-183897f07769

import Mathlib.Analysis.Complex.Basic

theorem solution (x : ℝ) : 11 ≤ abs (x - 3) + abs x + abs (x + 3) + abs (x + 5) := by
  have h1 := neg_abs_le (x - 3)
  have h2 := le_abs_self (x + 3)
  have h3 := neg_abs_le x
  have h4 := le_abs_self (x + 5)
  linarith
