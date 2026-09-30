-- Prove2me | solution 1 for lean_workbook_plus_48040
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:16:48.091853+00:00
-- url     : https://prove2.me/submissions/f2dc6d13-8654-4a94-8385-087974cea7c7

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution :
  (5:ℝ)^25 > 2^58 := by
  norm_num
