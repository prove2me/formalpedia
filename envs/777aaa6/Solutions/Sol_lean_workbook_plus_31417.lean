-- Prove2me | solution 1 for lean_workbook_plus_31417
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:18:40.528148+00:00
-- url     : https://prove2.me/submissions/e58aac93-d44e-494d-b274-42a90f021745

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution :
  1996 = 2^2 * 499 := by
  norm_num
