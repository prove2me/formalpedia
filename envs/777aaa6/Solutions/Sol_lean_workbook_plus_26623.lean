-- Prove2me | solution 1 for lean_workbook_plus_26623
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T23:00:28.225295+00:00
-- url     : https://prove2.me/submissions/c693d35f-1391-4e71-b9e1-43dbc1a1d223

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution (x : ℚ) : x = ⌊x⌋ + (x - ⌊x⌋) := by
  norm_num
