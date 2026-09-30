-- Prove2me | solution 1 for lean_workbook_plus_51336
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:17:40.668019+00:00
-- url     : https://prove2.me/submissions/36e0adb6-d148-4308-9cb4-3a0d9b0c6601

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : ∃ x : ℝ, x = 109.5 := by
  norm_num
