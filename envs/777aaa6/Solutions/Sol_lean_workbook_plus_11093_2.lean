-- Prove2me | solution 2 for lean_workbook_plus_11093
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:23:22.467648+00:00
-- url     : https://prove2.me/submissions/357a303c-aece-456f-b85b-a7514d2431f3

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y : ℝ) :
  Real.sqrt (x^2 + x * y + y^2) ≥ Real.sqrt (3 * x * y) := by
  intros
  apply Real.sqrt_le_sqrt
  nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg (x - y)]
