-- Prove2me | solution 1 for lean_workbook_plus_53494
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:37:07.604693+00:00
-- url     : https://prove2.me/submissions/da9d3607-806a-4594-ad8e-37f2064a1a02

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution :
  9^2 * 8 * 7 = 4536 := by
  norm_num
