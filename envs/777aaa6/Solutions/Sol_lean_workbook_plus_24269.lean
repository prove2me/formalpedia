-- Prove2me | solution 1 for lean_workbook_plus_24269
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:42:31.281301+00:00
-- url     : https://prove2.me/submissions/71901ce9-3048-4773-816d-e5ddb683c5a8

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : (1 + 1 / 16)^16 < 8 / 3 := by
  norm_num
