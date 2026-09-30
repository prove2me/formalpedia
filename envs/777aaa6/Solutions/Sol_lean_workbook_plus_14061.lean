-- Prove2me | solution 1 for lean_workbook_plus_14061
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:45:32.186452+00:00
-- url     : https://prove2.me/submissions/8fdaac3c-25bb-42d6-91ed-c99becf77496

import Mathlib.Analysis.Complex.Basic

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 2) : 1 / (a^2 + 3) + 1 / (b^2 + 3) ≤ 1 / 2 := by
  have h1 : 0 < a^2 + 3 := by positivity
  have h2 : 0 < b^2 + 3 := by positivity
  rw [div_add_div _ _ (ne_of_gt h1) (ne_of_gt h2), div_le_div_iff₀ (by positivity) (by norm_num)]
  have hb' : b = 2 - a := by linarith
  subst hb'
  nlinarith [sq_nonneg (a - 1), sq_nonneg (a * (2 - a)), mul_pos ha hb, sq_nonneg (a - 1), mul_nonneg (mul_pos ha hb).le (sq_nonneg (a - 1))]
