-- Prove2me | solution 1 for lean_workbook_plus_43770
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:24:20.160874+00:00
-- url     : https://prove2.me/submissions/c6e8c41f-0ef7-4dbf-979e-e7280676c4f2

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y z : ℝ) : y^4 * z^2 + z^4 * x^2 + x^4 * y^2 ≥ y * z * x * (z * x^2 + y^2 * x + z^2 * y) := by
  nlinarith [sq_nonneg (y^2*z-z^2*x),sq_nonneg (z^2*x-x^2*y),sq_nonneg (x^2*y-y^2*z)]
