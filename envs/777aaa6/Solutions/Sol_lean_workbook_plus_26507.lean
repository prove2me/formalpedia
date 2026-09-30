-- Prove2me | solution 1 for lean_workbook_plus_26507
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:16:50.087077+00:00
-- url     : https://prove2.me/submissions/4bb06f33-b099-4c96-a490-912d9ad820b9

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution (x : ℝ) : 0 * x = 0 := by
  norm_num
