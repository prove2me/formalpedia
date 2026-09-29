-- Prove2me | solution 1 for lean_workbook_plus_5168
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:54:07.10938+00:00
-- url     : https://prove2.me/submissions/d7cc6b2f-f560-40f3-bcdb-c2dcae58dc57

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b c d : ℝ) (hab : a + b + c + d = 0) : (a * b * c + b * c * d + c * d * a + d * a * b) ^ 2 = |(b * c - a * d) * (c * a - b * d) * (a * b - c * d)| := by
  have hd : d= -a-b-c := by linarith
  subst d
  have hid : (b*c-a*(-a-b-c))*(c*a-b*(-a-b-c))*(a*b-c*(-a-b-c)) = (a*b*c+b*c*(-a-b-c)+c*(-a-b-c)*a+(-a-b-c)*a*b)^2 := by ring
  rw [hid,abs_of_nonneg (sq_nonneg _)]
