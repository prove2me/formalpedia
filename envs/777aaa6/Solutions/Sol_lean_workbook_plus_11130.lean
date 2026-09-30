-- Prove2me | solution 1 for lean_workbook_plus_11130
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:42:33.509754+00:00
-- url     : https://prove2.me/submissions/b7cdcc47-a9f2-4fd2-97a1-6792657d7589

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : (1 : ℝ) - 1 / 2 = 1 / 2 := by
  norm_num
