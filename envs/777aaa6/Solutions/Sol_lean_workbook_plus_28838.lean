-- Prove2me | solution 1 for lean_workbook_plus_28838
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:42:41.048424+00:00
-- url     : https://prove2.me/submissions/341f0540-3c5f-41ef-829a-30106cbb2e2f

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution (x : ℤ) : ∃ y, y = x^2 - 1 := by
  norm_num
