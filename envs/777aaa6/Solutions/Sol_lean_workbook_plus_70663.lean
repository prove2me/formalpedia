-- Prove2me | solution 1 for lean_workbook_plus_70663
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:47:25.919426+00:00
-- url     : https://prove2.me/submissions/464367ea-a41a-4bda-bb0d-a6298c164915

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 2 ^ 15 + 1 ∣ 2 ^ 30 - 1 := by
  norm_num
