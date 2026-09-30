-- Prove2me | solution 1 for lean_workbook_plus_31366
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:16:25.31134+00:00
-- url     : https://prove2.me/submissions/f1494165-7d7c-4acc-a41f-2ec0f243bdcb

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : (-9)^2 = 81 := by
  norm_num
