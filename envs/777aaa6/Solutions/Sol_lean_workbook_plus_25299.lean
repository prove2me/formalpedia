-- Prove2me | solution 1 for lean_workbook_plus_25299
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:37:54.579593+00:00
-- url     : https://prove2.me/submissions/6cba2d8a-6c0f-428f-92ed-2c8233c46fdd

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 10^10 = 2^10 * 5^10 := by
  norm_num
