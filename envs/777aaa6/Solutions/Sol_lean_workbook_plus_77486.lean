-- Prove2me | solution 1 for lean_workbook_plus_77486
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T23:00:34.212411+00:00
-- url     : https://prove2.me/submissions/27c888b8-b4d5-47eb-b7d7-47779f0e5db2

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : (4:ℝ)^(80) > 2 * (3:ℝ)^(100) := by
  norm_num
