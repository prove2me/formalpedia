-- Prove2me | solution 1 for lean_workbook_plus_67838
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:47:26.678265+00:00
-- url     : https://prove2.me/submissions/ac815540-108e-4a46-959d-b897bc8a6324

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution (x y : ℤ) : x + y = x + y := by
  norm_num
