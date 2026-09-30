-- Prove2me | solution 1 for lean_workbook_plus_35982
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:15:44.961938+00:00
-- url     : https://prove2.me/submissions/d872a31e-9d5d-49ea-aa9a-cf51e50280f2

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 64 > 35 := by
  norm_num
