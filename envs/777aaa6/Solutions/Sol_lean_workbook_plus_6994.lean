-- Prove2me | solution 1 for lean_workbook_plus_6994
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:32:16.801185+00:00
-- url     : https://prove2.me/submissions/0b95fa76-4c72-4796-ae42-061bac71496f

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) (ha : a ^ 2 + b ^ 2 + c ^ 2 = 1) : a * b + b * c + c * a ≥ -1 / 2 := by
  nlinarith [sq_nonneg (a+b+c)]
