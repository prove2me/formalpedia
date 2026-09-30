-- Prove2me | solution 1 for lean_workbook_plus_8208
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:18:41.164032+00:00
-- url     : https://prove2.me/submissions/a3763738-9e4b-4041-8603-b854f2a883b4

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : (9 : ℝ) / 9 = 1 := by
  norm_num
