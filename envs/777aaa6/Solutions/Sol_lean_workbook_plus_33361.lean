-- Prove2me | solution 1 for lean_workbook_plus_33361
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T23:00:30.805857+00:00
-- url     : https://prove2.me/submissions/16ec0387-8b0d-4d8e-8209-5ba7472413b9

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution (h : 500 ≠ 0) : 500 / 2 = 250 := by
  norm_num
