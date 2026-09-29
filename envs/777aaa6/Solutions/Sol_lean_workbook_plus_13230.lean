-- Prove2me | solution 1 for lean_workbook_plus_13230
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:47:36.552888+00:00
-- url     : https://prove2.me/submissions/92f4b154-8521-4508-8f50-fbece919059f

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b c : ℝ) : Real.sqrt ((a^2 + b^2)/2 + (c - a)*(c - b)) ≥ (a + b)/2 := by
  apply Real.le_sqrt_of_sq_le
  nlinarith only [sq_nonneg (2*c-a-b)]
