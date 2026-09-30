-- Prove2me | solution 1 for lean_workbook_plus_31408
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T23:12:43.942688+00:00
-- url     : https://prove2.me/submissions/6b976766-fd0b-4e0d-bde3-ada1cd870cbd

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution (z : ℂ) (n : ℕ) : ‖z^n‖ = ‖z‖^n := by
  norm_num
