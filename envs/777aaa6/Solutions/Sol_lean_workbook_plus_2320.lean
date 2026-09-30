-- Prove2me | solution 1 for lean_workbook_plus_2320
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:47:20.487352+00:00
-- url     : https://prove2.me/submissions/c5875e24-77f8-4a08-b888-be33c2a59ad7

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution :
  (2^14 - 2^10) = 15360 := by
  norm_num
