-- Prove2me | solution 1 for lean_workbook_plus_50227
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:57:22.627479+00:00
-- url     : https://prove2.me/submissions/39a3573a-d4bd-4293-9f63-01b48a8debf1

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution (x : ℕ) : (41^2 - 40^2) = 81 := by
  norm_num
