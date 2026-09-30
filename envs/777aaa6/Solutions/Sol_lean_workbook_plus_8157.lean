-- Prove2me | solution 1 for lean_workbook_plus_8157
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:19:49.378302+00:00
-- url     : https://prove2.me/submissions/8b1f80b6-3a28-46bc-b18d-353876f226d6

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : ⌊(-15 : ℚ)/16⌋ = -1 := by
  norm_num
