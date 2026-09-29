-- Prove2me | solution 1 for lean_workbook_plus_18562
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:25:54.321526+00:00
-- url     : https://prove2.me/submissions/0bbf83f7-3078-4637-8f0e-a2f21dba30a1

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (a b c d x y : ℝ) : (b^2 + d^2) * x^2 - 2 * (a * b + c * d) * x * y + (a^2 + c^2) * y^2 ≥ 0 := by
  nlinarith [sq_nonneg (b * x - a * y), sq_nonneg (d * x - c * y)]
