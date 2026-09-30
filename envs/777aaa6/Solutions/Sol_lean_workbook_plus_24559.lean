-- Prove2me | solution 1 for lean_workbook_plus_24559
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T23:03:42.481494+00:00
-- url     : https://prove2.me/submissions/3bd777b6-069a-4eaf-992a-eb6f142018c3

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution :
  2 * 8 + 2 * 5 - 2 * 2 = 22 := by
  norm_num
