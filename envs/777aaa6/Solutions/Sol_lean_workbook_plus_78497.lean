-- Prove2me | solution 1 for lean_workbook_plus_78497
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:19:04.947756+00:00
-- url     : https://prove2.me/submissions/53e6c8e6-4403-4554-afce-736ce6791e23

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution (a : ℝ) : a * 0 = 0 := by
  norm_num
