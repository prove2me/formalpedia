-- Prove2me | solution 1 for lean_workbook_plus_30234
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:18:07.37253+00:00
-- url     : https://prove2.me/submissions/160693a3-57b6-4386-9d89-22c704baaab8

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 35 * 79 = 2765 := by
  norm_num
