-- Prove2me | solution 1 for lean_workbook_plus_415
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:41:07.422486+00:00
-- url     : https://prove2.me/submissions/23067918-ae1d-41d8-9745-be046e2dc5f3

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x * y * z = 1) : (x ^ 2 + y ^ 2 + z ^ 2) * (x ^ 4 + y ^ 4 + z ^ 4) ≤ 3 * (x ^ 6 + y ^ 6 + z ^ 6) := by
  intros
  nlinarith [sq_nonneg (x^2 - y^2), sq_nonneg (x^3 - y^3), sq_nonneg (x^2 - z^2), sq_nonneg (x^3 - z^3), sq_nonneg (y^2 - z^2), sq_nonneg (y^3 - z^3)]
