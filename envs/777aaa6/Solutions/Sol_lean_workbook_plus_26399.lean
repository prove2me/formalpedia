-- Prove2me | solution 1 for lean_workbook_plus_26399
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T23:12:44.614271+00:00
-- url     : https://prove2.me/submissions/29c6efd7-dce6-48c4-b177-ebd7db6dab5c

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution (x y : ℝ) : x^2 + y^2 + x*y ≥ 0 := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg x, sq_nonneg y]
