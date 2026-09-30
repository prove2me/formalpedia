-- Prove2me | solution 1 for lean_workbook_plus_1017
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:15:38.700249+00:00
-- url     : https://prove2.me/submissions/2f902121-4f2c-4081-9a83-832c2d916861

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 2 % 2 = 0 := by
  norm_num
