-- Prove2me | solution 1 for lean_workbook_plus_58811
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T23:03:30.998202+00:00
-- url     : https://prove2.me/submissions/a1be5955-c82a-4fdf-b79a-dd4e903b7c61

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : ¬∃ y : ℤ, 126 * y ^ 2 = 2009 := by
  omega
