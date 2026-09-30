-- Prove2me | solution 1 for lean_workbook_plus_66853
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:57:24.114503+00:00
-- url     : https://prove2.me/submissions/57b013e1-9c27-41a1-a574-775f79e87ff0

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 5^13 < 3^20 ∧ 3^20 < 11^10 := by
  norm_num
