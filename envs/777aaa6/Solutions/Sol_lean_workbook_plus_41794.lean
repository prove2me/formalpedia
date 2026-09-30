-- Prove2me | solution 1 for lean_workbook_plus_41794
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T23:12:35.60778+00:00
-- url     : https://prove2.me/submissions/7270b7fb-3c9c-4b1c-930f-f90a3210ab7b

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution (x : ℝ) : x + x = 4 → 2 * x = 4 := by
  intros; nlinarith [sq_nonneg x]
