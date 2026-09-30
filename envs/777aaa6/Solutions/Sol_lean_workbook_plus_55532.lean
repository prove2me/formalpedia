-- Prove2me | solution 1 for lean_workbook_plus_55532
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:15:40.91237+00:00
-- url     : https://prove2.me/submissions/9ae1f351-85a7-4562-99c1-0fe3a1d917c7

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 0 % 2 = 0 := by
  norm_num
