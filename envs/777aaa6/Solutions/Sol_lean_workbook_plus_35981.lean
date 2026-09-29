-- Prove2me | solution 1 for lean_workbook_plus_35981
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:38:57.834161+00:00
-- url     : https://prove2.me/submissions/5298046d-92ba-4574-9235-2e902a4edd18

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c : ℝ) : a ^ 6 + b ^ 6 + c ^ 6 - 6 * a * b * c ≥ 3 * (a * b * c - 1) ^ 2 - 3 := by
  intros
  nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (a^3 - b^3), sq_nonneg (a^2 - c^2), sq_nonneg (a^3 - c^3), sq_nonneg (b^2 - c^2), sq_nonneg (b^3 - c^3)]
