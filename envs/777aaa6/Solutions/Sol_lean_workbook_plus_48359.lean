-- Prove2me | solution 1 for lean_workbook_plus_48359
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:59:50.541358+00:00
-- url     : https://prove2.me/submissions/585218df-ba45-4040-aa58-65a912fa9400

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y z : ℝ) : x^2 + y^4 + z^8 ≥ 2*x + 4*y + 8*z - 11 := by
  nlinarith only [sq_nonneg (x-1),sq_nonneg (y^2-1),sq_nonneg (y-1),sq_nonneg (z^4-1),sq_nonneg (z^2-1),sq_nonneg (z-1)]
