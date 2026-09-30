-- Prove2me | solution 1 for lean_workbook_plus_9919
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:18:07.14119+00:00
-- url     : https://prove2.me/submissions/e20d5501-2e26-4458-b9d8-de1a96d3a0d7

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : √((-4 : ℝ) ^ 2) = 4 := by
  simp
