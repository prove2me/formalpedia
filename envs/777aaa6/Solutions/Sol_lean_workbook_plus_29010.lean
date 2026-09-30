-- Prove2me | solution 1 for lean_workbook_plus_29010
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:42:30.256564+00:00
-- url     : https://prove2.me/submissions/f48b453c-186f-43c3-bd21-9a0ea2d30e36

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution (x : ℝ) : x^2 + x + 1 > 0 := by
  nlinarith [sq_nonneg x]
