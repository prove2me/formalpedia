-- Prove2me | solution 1 for lean_workbook_plus_37127
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:50:03.445939+00:00
-- url     : https://prove2.me/submissions/611ff15f-ee30-417d-98eb-3944d3ed4852

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution :
  1998 = 2 * 3^3 * 37 := by
  norm_num
