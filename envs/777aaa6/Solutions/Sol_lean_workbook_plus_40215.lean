-- Prove2me | solution 1 for lean_workbook_plus_40215
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:52:26.557613+00:00
-- url     : https://prove2.me/submissions/84d88705-8510-46bc-bf1f-811385dded6d

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y z : ℝ) : (x ^ 3 + y ^ 3 + z ^ 3) ^ 2 ≥ 3 * (x ^ 3 * y ^ 3 + x ^ 3 * z ^ 3 + y ^ 3 * z ^ 3) := by
  intros
  nlinarith [sq_nonneg (x^2 - y^2), sq_nonneg (x^3 - y^3), sq_nonneg (x^2 - z^2), sq_nonneg (x^3 - z^3), sq_nonneg (y^2 - z^2), sq_nonneg (y^3 - z^3)]
