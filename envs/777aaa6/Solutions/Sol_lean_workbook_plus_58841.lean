-- Prove2me | solution 1 for lean_workbook_plus_58841
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:37:47.024038+00:00
-- url     : https://prove2.me/submissions/940edaa3-f5d8-4b7d-bb95-0ce0c5820f5c

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : (-23) * (-23) = 529 := by
  norm_num
