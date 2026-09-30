-- Prove2me | solution 1 for lean_workbook_plus_520
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:18:43.534985+00:00
-- url     : https://prove2.me/submissions/71a75104-e94f-4b1b-be94-ea08097123b7

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : (10 : ℝ)⁻¹ = 0.1 := by
  norm_num
