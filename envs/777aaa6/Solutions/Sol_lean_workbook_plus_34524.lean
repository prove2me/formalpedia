-- Prove2me | solution 1 for lean_workbook_plus_34524
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T23:12:40.148696+00:00
-- url     : https://prove2.me/submissions/4b6bfdd7-9c08-4122-952d-8aef4c198262

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution (R : ℚ) : R = 200/48 → R = 25/6 := by
  norm_num
