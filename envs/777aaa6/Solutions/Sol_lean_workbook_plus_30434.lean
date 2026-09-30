-- Prove2me | solution 1 for lean_workbook_plus_30434
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:15:39.792011+00:00
-- url     : https://prove2.me/submissions/e2827236-6d07-4c29-81e6-ebf2d40f62b6

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 1 + 1 = 2 := by
  norm_num
