-- Prove2me | solution 1 for lean_workbook_plus_34872
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:18:06.752289+00:00
-- url     : https://prove2.me/submissions/c7c154d2-e4d4-4036-ab93-1f38b8204542

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution (n : ℝ) : n ∣ 0 := by
  norm_num
