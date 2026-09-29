-- Prove2me | solution 1 for lean_workbook_plus_8048
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:48:56.230618+00:00
-- url     : https://prove2.me/submissions/d638bb57-9459-4f94-ab82-b8117cc3385c

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x : ℝ)
  (h₀ : 0 ≤ 5 - x^2) :
  Real.sqrt (5 - x^2) ≤ Real.sqrt 5 := by
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg x])
