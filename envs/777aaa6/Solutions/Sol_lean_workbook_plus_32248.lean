-- Prove2me | solution 1 for lean_workbook_plus_32248
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:37:51.676852+00:00
-- url     : https://prove2.me/submissions/389b4904-32b7-4f9f-8f74-3affe9fd2b9b

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 31 - 4 + 2 * 5 = 37 := by
  norm_num
