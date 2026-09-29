-- Prove2me | solution 1 for lean_workbook_plus_3174
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:47:11.078166+00:00
-- url     : https://prove2.me/submissions/7f8a6b8f-7c9f-477a-99f1-92ff36bf663c

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b c: ℝ) : a^2 + b^2 ≥ 2*a*b ∧ b^2 + c^2 ≥ 2*b*c ∧ a^2 + c^2 ≥ 2*a*c := by
  constructor
  · nlinarith [sq_nonneg (a-b)]
  constructor
  · nlinarith [sq_nonneg (b-c)]
  · nlinarith [sq_nonneg (a-c)]
