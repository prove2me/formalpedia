-- Prove2me | solution 1 for lean_workbook_plus_7235
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:19:48.532727+00:00
-- url     : https://prove2.me/submissions/bc2e6ceb-a604-44cd-b291-6fc5625d0e64

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution :
  (11 + 3) % 12 = 2 := by
  norm_num
