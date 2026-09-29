-- Prove2me | solution 1 for lean_workbook_plus_53382
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:55:42.912448+00:00
-- url     : https://prove2.me/submissions/41bbcf81-c231-49d6-b11a-02f7d641c04d

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x : ℝ) : ((Real.sqrt 5 - 1) / (Real.sqrt 5 + 1))^2 = (7 - 3 * Real.sqrt 5) / 2 := by
  have hs : (Real.sqrt 5)^2 = 5 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 5+1 ≠ 0 := by positivity
  have he : (Real.sqrt 5-1)/(Real.sqrt 5+1) = (3-Real.sqrt 5)/2 := by
    apply (div_eq_iff hn).2
    nlinarith
  rw [he]
  nlinarith
