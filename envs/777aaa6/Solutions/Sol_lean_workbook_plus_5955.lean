-- Prove2me | solution 1 for lean_workbook_plus_5955
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:37:11.637712+00:00
-- url     : https://prove2.me/submissions/fb81156b-b892-4123-aeda-2549ded620f1

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 31 ∣ 5^31 + 5^17 + 1 := by
  norm_num
