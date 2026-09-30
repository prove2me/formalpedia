-- Prove2me | solution 1 for lean_workbook_plus_47094
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:16:47.164396+00:00
-- url     : https://prove2.me/submissions/3355ed80-4aac-4138-8a02-f3db3fae8e06

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution (a : ℝ) : a + 0 = a := by
  norm_num
