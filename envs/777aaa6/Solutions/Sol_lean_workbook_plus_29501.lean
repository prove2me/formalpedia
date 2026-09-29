-- Prove2me | solution 1 for lean_workbook_plus_29501
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:21:12.787157+00:00
-- url     : https://prove2.me/submissions/5099feec-780f-462e-a1a2-69844345cb43

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (f : ℝ → ℝ) (f_def : ∀ x, f x = x^3 - 20 * x^2 + 75 * x) : f 2 = 78 := by
  rw [f_def]
  norm_num
