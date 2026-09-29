-- Prove2me | solution 1 for lean_workbook_plus_69332
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:32:42.769034+00:00
-- url     : https://prove2.me/submissions/afd30ed9-b352-4835-b84c-e293bb346c4b

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y z : ℝ) : x ^ 6 + y ^ 6 + z ^ 6 ≥ 3 * (x * y * z) ^ 2 := by
  intros
  nlinarith [sq_nonneg (x^2 - y^2), sq_nonneg (x^3 - y^3), sq_nonneg (x^2 - z^2), sq_nonneg (x^3 - z^3), sq_nonneg (y^2 - z^2), sq_nonneg (y^3 - z^3)]
