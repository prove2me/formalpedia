-- Prove2me | solution 1 for lean_workbook_plus_46334
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:18:05.870117+00:00
-- url     : https://prove2.me/submissions/e4631d6e-57af-4507-84fc-71ce8651b2e1

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution (k : ℕ) : k = k := by
  norm_num
