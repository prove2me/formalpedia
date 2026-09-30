-- Prove2me | solution 1 for lean_workbook_plus_71286
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:06:43.824787+00:00
-- url     : https://prove2.me/submissions/38b44a39-3052-41ea-9422-61e5209fb197

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

private theorem scalar_bound (t : ℝ) : 3*t^4 ≤ 1+2*t^6 := by
  have hpos : 0 ≤ 2*t^2+1 := by nlinarith only [sq_nonneg t]
  have hp := mul_nonneg (sq_nonneg (t^2-1)) hpos
  nlinarith only [hp]

theorem solution (x y z : ℝ) : 3+2*(x^6+y^6+z^6) ≥ 3*(x^4+y^4+z^4) := by
  nlinarith only [scalar_bound x, scalar_bound y, scalar_bound z]
