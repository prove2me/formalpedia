-- Prove2me | solution 1 for lean_workbook_plus_14126
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:27:36.838651+00:00
-- url     : https://prove2.me/submissions/e82e5ff7-fbe6-4dba-9d62-d69c32ed6e79

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (a b : ℝ) : (2 * a + 2 * b) ^ 2 ≥ b * (4 * a + 3 * b) := by
  nlinarith [sq_nonneg (2*a+b)]
