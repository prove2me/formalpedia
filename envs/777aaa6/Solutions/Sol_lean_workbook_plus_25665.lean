-- Prove2me | solution 1 for lean_workbook_plus_25665
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T23:00:17.350281+00:00
-- url     : https://prove2.me/submissions/e7c42d9f-bcdc-4651-89d6-4b1af2712ae3

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 2^10 = 1024 → 2^20 = 1024^2 := by
  norm_num
