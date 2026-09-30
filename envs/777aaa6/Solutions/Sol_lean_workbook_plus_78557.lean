-- Prove2me | solution 1 for lean_workbook_plus_78557
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:42:37.102535+00:00
-- url     : https://prove2.me/submissions/2207b3c9-f981-4a21-918c-4a2847269315

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution :
  (16 : ℚ) / 52 = 4 / 13 := by
  norm_num
