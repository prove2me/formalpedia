-- Prove2me | solution 1 for lean_workbook_plus_38899
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T23:12:36.296292+00:00
-- url     : https://prove2.me/submissions/676215e4-1633-45ed-9513-0a75b9c84c8c

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution (z w : ℂ) : ‖z * w‖ = ‖z‖ * ‖w‖ := by
  norm_num
