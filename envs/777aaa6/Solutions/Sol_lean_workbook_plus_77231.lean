-- Prove2me | solution 1 for lean_workbook_plus_77231
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:57:28.778635+00:00
-- url     : https://prove2.me/submissions/c94a6c81-edf9-4f71-a60c-5067aba3d6c6

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution (a : ℤ) (ha : a ≠ 0) : a ∣ a := by
  norm_num
