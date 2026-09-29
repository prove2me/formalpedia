-- Prove2me | solution 1 for lean_workbook_plus_22402
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:04:55.015124+00:00
-- url     : https://prove2.me/submissions/6fdef9bd-76f5-4183-a59a-5f1ef840b2d1

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x : ℝ) :
  (x^4 + 1) / (x^6 + 1) = 1 / 3 * (x^2 + 1) / (x^4 - x^2 + 1) + 2 / (3 * (x^2 + 1)) := by
  have hq : 0<x^4-x^2+1 := by nlinarith only [sq_nonneg (x^2-1/2)]
  field_simp (disch := first | positivity | linarith)
  <;> ring
