-- Prove2me | solution 1 for lean_workbook_plus_62582
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:17:55.975185+00:00
-- url     : https://prove2.me/submissions/bfafa83a-985c-4405-b067-25e50224203b

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 1 - (-1) = 2 := by
  norm_num
