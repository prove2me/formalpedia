-- Prove2me | solution 1 for lean_workbook_plus_35150
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:37:49.906657+00:00
-- url     : https://prove2.me/submissions/05cb98c3-b065-42a7-bd1d-251ea67c5a39

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 99 ^ 100 > 100 ^ 99 := by
  norm_num
