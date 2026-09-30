-- Prove2me | solution 1 for lean_workbook_plus_49912
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T23:03:48.991849+00:00
-- url     : https://prove2.me/submissions/239f460d-fa62-40bc-a4b7-a01df1adc8db

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution (a b c : ℝ) : (a+b+c-3)^2 ≥ 0 := by
  positivity
