-- Prove2me | solution 1 for lean_workbook_plus_58041
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:37:46.26749+00:00
-- url     : https://prove2.me/submissions/b071b6aa-b21c-4352-940b-25a3b475ca18

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution (x : ℚ) : (x : ℝ) = x := by
  norm_num
