-- Prove2me | solution 1 for lean_workbook_plus_10947
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:19:03.762687+00:00
-- url     : https://prove2.me/submissions/37611d08-6cff-49f6-94ca-2fe1829d6628

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 29 ∣ 2^90 + 5^90 := by
  norm_num
