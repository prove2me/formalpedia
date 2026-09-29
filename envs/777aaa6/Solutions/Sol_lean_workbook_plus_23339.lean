-- Prove2me | solution 1 for lean_workbook_plus_23339
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:13:10.469922+00:00
-- url     : https://prove2.me/submissions/2b1cb0e2-4981-4c47-9808-66a273ef93b4

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b : ℝ) (ha : a^3 - 3*a^2 + 5*a - 17 = 0) (hb : b^3 - 3*b^2 + 5*b + 11 = 0) : a + b = 2 := by
  have hf : (a+b-2)*((a-1)^2-(a-1)*(b-1)+(b-1)^2+2)=0 := by nlinarith [ha,hb]
  have hp : 0 < (a-1)^2-(a-1)*(b-1)+(b-1)^2+2 := by nlinarith [sq_nonneg (a-b),sq_nonneg (a-1),sq_nonneg (b-1)]
  have hz := (mul_eq_zero.mp hf).resolve_right (ne_of_gt hp)
  linarith
