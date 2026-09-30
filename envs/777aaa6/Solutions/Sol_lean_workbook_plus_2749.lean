-- Prove2me | solution 1 for lean_workbook_plus_2749
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:36:52.34907+00:00
-- url     : https://prove2.me/submissions/c092394f-61ae-4f15-80f3-34167186794b

import Mathlib

theorem solution (a b : ℝ) : (a + b) / (1 + a ^ 2 + b ^ 2) ≤ 1 / Real.sqrt 2 := by
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [sq_nonneg (a - Real.sqrt 2 / 2), sq_nonneg (b - Real.sqrt 2 / 2),
    Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
