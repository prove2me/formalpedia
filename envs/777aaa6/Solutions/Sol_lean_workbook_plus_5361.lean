-- Prove2me | solution 1 for lean_workbook_plus_5361
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:52:34.664158+00:00
-- url     : https://prove2.me/submissions/27594d1f-9541-426f-9a61-15fcbb9bb4b4

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y z : ℝ) : (4 * (x ^ 2 + y ^ 2 + z ^ 2)) ^ 3 ≥ 27 * (2 * x ^ 2 + y ^ 2 + z ^ 2) * (2 * y ^ 2 + z ^ 2 + x ^ 2) * (2 * z ^ 2 + x ^ 2 + y ^ 2) := by
  intros
  nlinarith [sq_nonneg (x^2 - y^2), sq_nonneg (x^3 - y^3), sq_nonneg (x^2 - z^2), sq_nonneg (x^3 - z^3), sq_nonneg (y^2 - z^2), sq_nonneg (y^3 - z^3)]
