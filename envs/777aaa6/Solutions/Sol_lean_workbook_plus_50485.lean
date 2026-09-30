-- Prove2me | solution 1 for lean_workbook_plus_50485
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:53:25.239112+00:00
-- url     : https://prove2.me/submissions/b14603a7-9f6e-46dd-8eee-cfa77af0fb36

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution (b c : ℝ) : (b - c) ^ 2 ≥ 0 := by
  positivity
