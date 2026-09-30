-- Prove2me | solution 1 for lean_workbook_plus_45985
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:19:02.329851+00:00
-- url     : https://prove2.me/submissions/756f72fd-c10c-4e0c-9f4f-a0049747fa59

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 13 ∣ 2^70 + 3^70 := by
  norm_num
