-- Prove2me | solution 1 for lean_workbook_plus_24191
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:42:38.184086+00:00
-- url     : https://prove2.me/submissions/49899646-0036-4e73-b9ea-9179cd8c9196

import Mathlib.Analysis.Complex.Basic

theorem solution (a b k : ℝ) (h₁ : 0 < k) (h₂ : (a + Real.sqrt (a^2 + 1)) * (b + Real.sqrt (b^2 + 1)) = k) : (1 + k) * (a + b) = (k - 1) * (Real.sqrt (a^2 + 1) + Real.sqrt (b^2 + 1)) := by
  have hA : Real.sqrt (a^2 + 1) ^ 2 = a^2 + 1 := Real.sq_sqrt (by positivity)
  have hB : Real.sqrt (b^2 + 1) ^ 2 = b^2 + 1 := Real.sq_sqrt (by positivity)
  rw [← h₂]
  linear_combination (-(b + Real.sqrt (b^2 + 1))) * hA + (-(a + Real.sqrt (a^2 + 1))) * hB
