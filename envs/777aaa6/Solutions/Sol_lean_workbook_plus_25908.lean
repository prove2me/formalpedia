-- Prove2me | solution 1 for lean_workbook_plus_25908
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:18:57.422528+00:00
-- url     : https://prove2.me/submissions/4e855781-fab8-4b19-a1bd-df0c4c60f0cf

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 98^101 > 99^100 := by
  norm_num
