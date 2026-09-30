-- Prove2me | solution 1 for lean_workbook_plus_71947
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:15:43.534362+00:00
-- url     : https://prove2.me/submissions/8b4f8847-4f94-49f2-a3e1-d236f676e998

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 2 + 2 = 4 := by
  norm_num
