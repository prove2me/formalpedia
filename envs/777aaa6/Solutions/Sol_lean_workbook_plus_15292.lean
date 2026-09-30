-- Prove2me | solution 1 for lean_workbook_plus_15292
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T23:00:30.122917+00:00
-- url     : https://prove2.me/submissions/de69e19f-291a-4d98-b175-10f965871e30

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution :
  1 * (2006 / 2) + 1 = 1004 := by
  norm_num
