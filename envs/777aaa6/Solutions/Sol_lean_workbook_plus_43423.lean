-- Prove2me | solution 1 for lean_workbook_plus_43423
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T23:03:41.833171+00:00
-- url     : https://prove2.me/submissions/cb38ad13-d7c0-46f3-855e-8e82ffaba2e2

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : (1.8582 : ℝ) / 1.05 > 1.7697 := by
  norm_num
