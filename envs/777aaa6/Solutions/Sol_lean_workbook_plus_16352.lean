-- Prove2me | solution 1 for lean_workbook_plus_16352
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:14:40.603621+00:00
-- url     : https://prove2.me/submissions/1d2947e2-6f5b-43e3-97e1-dbac88f09413

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x y z : ℝ) : (x^2 / y^2 + y^2 / z^2 + z^2 / x^2) * (1 + 1 + 1) ≥ (x / y + y / z + z / x)^2 := by
  simp only [← div_pow]
  nlinarith only [sq_nonneg (x/y-y/z), sq_nonneg (y/z-z/x), sq_nonneg (z/x-x/y)]
