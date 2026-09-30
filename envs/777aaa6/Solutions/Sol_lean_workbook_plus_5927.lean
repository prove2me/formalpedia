-- Prove2me | solution 1 for lean_workbook_plus_5927
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:17:42.034514+00:00
-- url     : https://prove2.me/submissions/23ed5d22-74de-4ed0-bf8b-fa08650f3b41

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 2^2 * 2^2 - 1 = 15 := by
  norm_num
