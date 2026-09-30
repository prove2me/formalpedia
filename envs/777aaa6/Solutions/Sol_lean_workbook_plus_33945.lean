-- Prove2me | solution 1 for lean_workbook_plus_33945
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:13:45.750331+00:00
-- url     : https://prove2.me/submissions/6baede78-bd51-4e58-9fd6-15626fb91598

import Mathlib.Analysis.Complex.Basic

theorem solution (f : ℝ → ℝ) (x : ℝ) (f_of_le : x ≤ -1 / 2 → f x = x - 2) (f_of_ge : -1 / 2 ≤ x → f x = 5 * x) : f x = if x ≤ -1 / 2 then x - 2 else 5 * x := by
  split_ifs with h
  · exact f_of_le h
  · exact f_of_ge (le_of_lt (not_le.mp h))
