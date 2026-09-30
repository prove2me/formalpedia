-- Prove2me | solution 1 for lean_workbook_plus_13240
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T23:00:26.402248+00:00
-- url     : https://prove2.me/submissions/e492a1af-57b0-4fce-853b-b3ac997306c4

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution (a : ℤ) (h : a^2 = 0) : a = 0 := by
  nlinarith
