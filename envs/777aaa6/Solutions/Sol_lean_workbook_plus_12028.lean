-- Prove2me | solution 1 for lean_workbook_plus_12028
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:53:23.520852+00:00
-- url     : https://prove2.me/submissions/f252712d-48c8-479b-bb41-88db6a104a76

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : (5 / 4 : ℝ) ^ 31 > 2 ^ 7 := by
  norm_num
