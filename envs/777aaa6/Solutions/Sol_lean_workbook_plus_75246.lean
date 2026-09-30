-- Prove2me | solution 1 for lean_workbook_plus_75246
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:36:35.911934+00:00
-- url     : https://prove2.me/submissions/b58c0889-e072-4b77-a6e5-9e475d80a02f

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

theorem solution (y : ℝ) (hy : -1/2 < y ∧ y < 0) : |y| > |2*y^2| := by
  rw [abs_of_neg hy.2, abs_of_nonneg (by positivity : 0 ≤ 2*y^2)]
  have hprod : 0 < (-y)*(y+1/2) := mul_pos (by linarith) (by linarith)
  nlinarith
