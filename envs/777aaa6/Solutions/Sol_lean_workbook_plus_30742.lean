-- Prove2me | solution 1 for lean_workbook_plus_30742
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T23:03:35.765599+00:00
-- url     : https://prove2.me/submissions/140d2d1d-3f81-480e-af34-9b3ce9144c83

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution (n : ℝ) (hn : n ≠ 0) : n^0 = 1 := by
  norm_num
