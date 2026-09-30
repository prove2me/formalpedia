-- Prove2me | solution 1 for lean_workbook_plus_63887
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:15:42.913682+00:00
-- url     : https://prove2.me/submissions/d7d40115-f7c2-4829-837a-ca4bc42652dd

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 7 + 7 = 14 := by
  norm_num
