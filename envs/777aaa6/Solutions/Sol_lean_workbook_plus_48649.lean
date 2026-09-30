-- Prove2me | solution 1 for lean_workbook_plus_48649
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:15:40.340755+00:00
-- url     : https://prove2.me/submissions/77c85144-afd7-4b14-a786-c4ed5f2534fb

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 32 % 9 = 5 := by
  norm_num
