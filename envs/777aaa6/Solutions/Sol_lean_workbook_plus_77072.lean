-- Prove2me | solution 1 for lean_workbook_plus_77072
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:37:16.091844+00:00
-- url     : https://prove2.me/submissions/8d89cc90-9f7a-460a-a480-19aec8d61846

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution :
  (3^100) % 1000 = 1 := by
  norm_num
