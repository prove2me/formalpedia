-- Prove2me | solution 1 for lean_workbook_plus_24239
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:15:36.618346+00:00
-- url     : https://prove2.me/submissions/53c3fb7e-47cf-41bc-b0cc-a2b675d6e368

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 8 + 7 = 15 := by
  norm_num
