-- Prove2me | solution 1 for lean_workbook_plus_18048
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:19:36.525388+00:00
-- url     : https://prove2.me/submissions/06e9e35a-ef19-4de4-b049-98277e72e4e1

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b : ℝ) : a^4 * b^2 + a^2 * b^4 + 1 ≥ a^3 * b^3 + a * b^2 + a^2 * b := by
  nlinarith [sq_nonneg (a^2*b-a*b^2),sq_nonneg (a*b^2-1),sq_nonneg (a^2*b-1)]
