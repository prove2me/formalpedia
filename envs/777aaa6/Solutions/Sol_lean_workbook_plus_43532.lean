-- Prove2me | solution 1 for lean_workbook_plus_43532
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:59:29.870719+00:00
-- url     : https://prove2.me/submissions/eebadb80-fa76-4eff-9172-d4ca8905bf2a

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution : ∀ n : ℤ, 8 * n ^ 2 + 16 * n + 9 > 0 := by
  intro n
  nlinarith [sq_nonneg (n+1)]
