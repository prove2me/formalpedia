-- Prove2me | solution 1 for lean_workbook_plus_22404
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:19:16.210444+00:00
-- url     : https://prove2.me/submissions/4ca7ee6b-2b36-48f4-9327-6d31728a3c40

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution :
  (2^2006) % 7 = 4 := by
  omega
