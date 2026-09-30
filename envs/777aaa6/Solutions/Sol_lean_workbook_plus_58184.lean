-- Prove2me | solution 1 for lean_workbook_plus_58184
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:18:14.077364+00:00
-- url     : https://prove2.me/submissions/4bc10aa3-0d51-45d5-aa51-ec3014cf1ad5

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 56 - 38 = 18 := by
  norm_num
