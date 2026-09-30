-- Prove2me | solution 1 for lean_workbook_plus_32600
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:37:52.7713+00:00
-- url     : https://prove2.me/submissions/81528c8b-daef-4a7e-a12d-2ae1e4963379

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 3^4 ∣ 19^93 - 13^99 := by
  norm_num
