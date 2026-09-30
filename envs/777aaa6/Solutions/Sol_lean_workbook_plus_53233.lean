-- Prove2me | solution 1 for lean_workbook_plus_53233
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:47:24.646776+00:00
-- url     : https://prove2.me/submissions/d209284f-0008-4b7b-879e-4a51bb74a867

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution :
  (8 : ℝ) / 28 = 2 / 7 := by
  norm_num
