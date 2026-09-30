-- Prove2me | solution 1 for lean_workbook_plus_13480
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T23:00:12.95139+00:00
-- url     : https://prove2.me/submissions/a5fa6d25-01b1-493f-806b-f06663de1d73

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution :
  (2017^167) % 10000 = 9073 := by
  norm_num
