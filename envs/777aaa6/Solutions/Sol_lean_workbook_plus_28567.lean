-- Prove2me | solution 1 for lean_workbook_plus_28567
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:17:58.565213+00:00
-- url     : https://prove2.me/submissions/6c4b3dd0-aafd-414a-9590-e076bfb09ac6

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution (a : ℤ) : a ∣ a := by
  norm_num
