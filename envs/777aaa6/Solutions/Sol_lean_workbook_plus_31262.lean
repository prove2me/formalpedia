-- Prove2me | solution 1 for lean_workbook_plus_31262
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:19:03.179207+00:00
-- url     : https://prove2.me/submissions/6a1d0d89-c582-474a-9ad8-3b86b8a3b2d2

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 13 ∣ 2^30 + 3^60 := by
  norm_num
