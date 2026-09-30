-- Prove2me | solution 1 for lean_workbook_plus_53381
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:37:47.745036+00:00
-- url     : https://prove2.me/submissions/1657c3f4-008e-4438-9b2c-8cf790f0b6f5

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : (-1 : ℤ) * (-1) = 1 := by
  norm_num
