-- Prove2me | solution 1 for lean_workbook_plus_79679
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:19:11.67466+00:00
-- url     : https://prove2.me/submissions/28ea774b-e7bb-494f-a15e-be99d8176e13

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution :
  (7^1996) % 10 = 1 := by
  omega
