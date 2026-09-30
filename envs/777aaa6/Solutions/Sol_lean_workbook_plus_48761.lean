-- Prove2me | solution 1 for lean_workbook_plus_48761
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:53:19.128493+00:00
-- url     : https://prove2.me/submissions/a4260874-90ef-44c9-adeb-adcd2553fde5

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution :
  6 - 2 + (5 - (-6)) = 15 := by
  norm_num
