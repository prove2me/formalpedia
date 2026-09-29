-- Prove2me | solution 1 for lean_workbook_plus_20797
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:29:43.584579+00:00
-- url     : https://prove2.me/submissions/448d1fb6-2965-4018-9f6b-b1813912a4c9

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c d : ℝ) (h : a + b + c + d = 1) :
  a * b + a * c + a * d + b * c + b * d + c * d ≤ 3 / 8 := by
  nlinarith [sq_nonneg (a-b),sq_nonneg (a-c),sq_nonneg (a-d),sq_nonneg (b-c),sq_nonneg (b-d),sq_nonneg (c-d)]
