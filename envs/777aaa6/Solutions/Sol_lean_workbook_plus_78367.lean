-- Prove2me | solution 1 for lean_workbook_plus_78367
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:48:07.798939+00:00
-- url     : https://prove2.me/submissions/fb7384c3-2753-4bac-9541-f1fe90cc8e3f

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution :
  6 * (142857) = 857142 := by
  norm_num
