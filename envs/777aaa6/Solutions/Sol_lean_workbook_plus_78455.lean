-- Prove2me | solution 1 for lean_workbook_plus_78455
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:02:56.241438+00:00
-- url     : https://prove2.me/submissions/46eeb530-490a-4255-acbf-fea0779b0f95

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ x y z : ℝ, 8 * (x * y * z) ^ 2 ≤ (x ^ 2 + y ^ 2) * (y ^ 2 + z ^ 2) * (z ^ 2 + x ^ 2) := by
  intro x y z
  intros
  nlinarith [sq_nonneg (x^2 - y^2), sq_nonneg (x^3 - y^3), sq_nonneg (x^2 - z^2), sq_nonneg (x^3 - z^3), sq_nonneg (y^2 - z^2), sq_nonneg (y^3 - z^3)]
