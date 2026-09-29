-- Prove2me | solution 1 for lean_workbook_plus_29484
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:35:38.315533+00:00
-- url     : https://prove2.me/submissions/7d1653db-ba1b-4d32-9f34-9041a367e912

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℝ) (hx : 5/9 ≤ x) : 3 * x ^ 4 + 3 * x ^ 2 + 5 > 9 * x := by
  clear hx
  nlinarith [sq_nonneg (x^2-1/2), sq_nonneg (x-3/4)]
