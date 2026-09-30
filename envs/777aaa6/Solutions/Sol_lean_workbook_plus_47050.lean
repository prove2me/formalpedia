-- Prove2me | solution 1 for lean_workbook_plus_47050
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T23:03:33.767097+00:00
-- url     : https://prove2.me/submissions/7d112910-174c-46cd-b7b3-d0b03990efbf

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution (a : ℝ) (ha : 0 < a) : 0 < a⁻¹ := by
  positivity
