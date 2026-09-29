-- Prove2me | solution 1 for lean_workbook_plus_40995
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:58:44.044163+00:00
-- url     : https://prove2.me/submissions/a22f48e7-b98e-4c08-b62b-834cca0ff763

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y z : ℝ) : (4 * (x + y + z) - x * y * z) ^ 2 + 4 * (x * y + y * z + z * x - 4) ^ 2 ≥ 8 := by
  intros
  nlinarith [sq_nonneg (x * y), sq_nonneg (x * z), sq_nonneg (y * z), sq_nonneg (x^2 - y^2), sq_nonneg (x^2 - z^2), sq_nonneg (y^2 - z^2)]
