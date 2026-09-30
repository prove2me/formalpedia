-- Prove2me | solution 1 for lean_workbook_plus_11897
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:18:04.345532+00:00
-- url     : https://prove2.me/submissions/cbbfac76-36bc-41d9-af05-1a67cfc59326

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : (2^3)^2 = 64 := by
  norm_num
