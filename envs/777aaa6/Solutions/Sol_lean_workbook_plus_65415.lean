-- Prove2me | solution 1 for lean_workbook_plus_65415
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:37:45.417294+00:00
-- url     : https://prove2.me/submissions/0474c36a-8a84-4fce-99fe-14cb21f8e6f6

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 162 ∣ 19^93 - 13^99 := by
  norm_num
