-- Prove2me | solution 1 for lean_workbook_plus_15925
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:17:56.724225+00:00
-- url     : https://prove2.me/submissions/1bd9fbd8-9170-4005-a03f-cda8c53a2302

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 75^2 = 5625 := by
  norm_num
