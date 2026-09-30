-- Prove2me | solution 1 for lean_workbook_plus_2208
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:18:00.221945+00:00
-- url     : https://prove2.me/submissions/aee11442-01ef-4a46-830b-cc551986fa9c

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : (-1 : ℤ)^0 = 1 := by
  norm_num
