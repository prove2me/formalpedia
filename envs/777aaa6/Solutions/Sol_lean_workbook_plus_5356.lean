-- Prove2me | solution 1 for lean_workbook_plus_5356
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:18:42.829215+00:00
-- url     : https://prove2.me/submissions/20b9eae0-5643-44f1-a021-ea644cc50ba4

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 5 ∣ 3^3 - 3 + 1 := by
  norm_num
