-- Prove2me | solution 1 for lean_workbook_plus_3076
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T23:12:29.269419+00:00
-- url     : https://prove2.me/submissions/0d7488aa-3580-4cd2-ba45-83df2307ae55

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution (a b : ℝ) : a / b = 1 / (b / a) := by
  norm_num
