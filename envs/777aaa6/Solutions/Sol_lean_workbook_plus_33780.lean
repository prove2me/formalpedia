-- Prove2me | solution 1 for lean_workbook_plus_33780
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:55:23.774718+00:00
-- url     : https://prove2.me/submissions/0dc7068f-6da2-4a81-87c4-3a38d84d8189

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x y z : ℝ) : 4 * (x^6 + y^6 + z^6) ≥ 4 * (x^3 * y^3 + y^3 * z^3 + z^3 * x^3) := by
  nlinarith [sq_nonneg (x^3-y^3), sq_nonneg (y^3-z^3), sq_nonneg (z^3-x^3)]
