-- Prove2me | solution 1 for lean_workbook_plus_7254
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:45:54.483874+00:00
-- url     : https://prove2.me/submissions/0a87e772-1ceb-4f94-9ceb-80c80a4ee720

import Mathlib.Analysis.Complex.Basic

theorem solution (a : ℝ) (h : a > 0) : a^3 + 11 > 9*a := by
  nlinarith [mul_nonneg h.le (sq_nonneg (a - 7/4)), sq_nonneg (a - 193/112), sq_nonneg (a - 2), sq_nonneg (a - 1)]
