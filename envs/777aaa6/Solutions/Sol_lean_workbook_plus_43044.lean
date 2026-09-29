-- Prove2me | solution 1 for lean_workbook_plus_43044
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:06:28.259122+00:00
-- url     : https://prove2.me/submissions/06f1313b-3804-4c1c-a275-7f22b07c8abb

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (x : ℝ) (hx : x ≥ 3) : (x - 3) * (x^3 + 3 * x^2 + 9 * x - 27) ≥ 0 := by
  apply mul_nonneg (by linarith : 0 ≤ x - 3)
  have hx0 : 0 ≤ x := by linarith
  have hx3 : 0 ≤ x ^ 3 := by positivity
  nlinarith [sq_nonneg x]
