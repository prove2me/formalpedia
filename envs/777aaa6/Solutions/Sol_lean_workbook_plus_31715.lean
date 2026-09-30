-- Prove2me | solution 1 for lean_workbook_plus_31715
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:42:41.590338+00:00
-- url     : https://prove2.me/submissions/d547af82-dff1-4eab-a2a6-23ccf10da247

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : ∀ a : ℤ, a^2 = 0 → a = 0 := by
  norm_num
