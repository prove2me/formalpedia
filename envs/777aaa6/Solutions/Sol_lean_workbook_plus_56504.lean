-- Prove2me | solution 1 for lean_workbook_plus_56504
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:19:01.54477+00:00
-- url     : https://prove2.me/submissions/235d268f-f55d-497d-8477-e6d90612bbeb

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution :
  (2^8) % 11 = 3 := by
  norm_num
