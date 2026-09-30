-- Prove2me | solution 1 for lean_workbook_plus_72944
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:57:27.916748+00:00
-- url     : https://prove2.me/submissions/66174fa4-dc6d-426a-89a6-e571140d8cb2

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution (b : ℝ) : 6/5 * b = 1.20 * b := by
  norm_num
