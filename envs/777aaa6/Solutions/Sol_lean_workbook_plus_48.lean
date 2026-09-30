-- Prove2me | solution 1 for lean_workbook_plus_48
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T23:03:35.147407+00:00
-- url     : https://prove2.me/submissions/993a142a-1264-41a3-b233-cd535eb32ba4

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution :
  1 - (25 : ℝ) / 64 = 39 / 64 := by
  norm_num
