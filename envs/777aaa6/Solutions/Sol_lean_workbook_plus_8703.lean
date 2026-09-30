-- Prove2me | solution 1 for lean_workbook_plus_8703
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:19:12.931198+00:00
-- url     : https://prove2.me/submissions/533d186c-3c3a-47ec-897b-5d818ab28854

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : (4 - 4) * 9 + 6 = 6 := by
  norm_num
