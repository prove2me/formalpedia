-- Prove2me | solution 1 for lean_workbook_plus_75406
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:19:58.903116+00:00
-- url     : https://prove2.me/submissions/c3d1a38a-76dc-4947-8ceb-cb2e2087db92

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : √((-1 : ℝ) ^ 2) = 1 := by
  simp
