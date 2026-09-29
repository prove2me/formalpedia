-- Prove2me | solution 1 for lean_workbook_plus_35207
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:07:06.636862+00:00
-- url     : https://prove2.me/submissions/c94ecf41-2cbd-4ec6-bc67-b8fde15b4b0c

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℝ)
  (h₀ : 0 < x)
  (h₁ : x ≤ 1) :
  3 * Real.sqrt 3 / 16 ≤ x^2 * Real.sqrt 3 / 4 + (1 - x) * Real.sqrt 3 / 4 := by
  have hp := mul_nonneg (Real.sqrt_nonneg 3) (sq_nonneg (x-1/2))
  nlinarith only [hp]
