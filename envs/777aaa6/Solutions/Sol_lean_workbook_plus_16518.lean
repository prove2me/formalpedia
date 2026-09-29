-- Prove2me | solution 1 for lean_workbook_plus_16518
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:21:38.409083+00:00
-- url     : https://prove2.me/submissions/6d6282b1-dc74-4b97-a02b-8dc7e763b271

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y z : ℝ) :
  (x^2*y^2+y^2*z^2+z^2*x^2)^2 ≥ 3*x^2*y^2*z^2*(x*y+y*z+z*x) := by
  intros
  have h : (0 : ℝ) ≤ ((x^2*y^2+y^2*z^2+z^2*x^2)^2) - (3*x^2*y^2*z^2*(x*y+y*z+z*x)) := by
    calc
      0 ≤ (1 : ℝ) * ((((y ^ 2) * (z ^ 2)) + ((-1) * y * z * (x ^ 2))))^2 + ((1 / 2) : ℝ) * (((x * y * (z ^ 2)) + ((-1) * x * z * (y ^ 2))))^2 + ((1 / 2) : ℝ) * (((x * y * (z ^ 2)) + ((-1) * y * z * (x ^ 2))))^2 + (1 : ℝ) * ((((-1) * (x ^ 2) * (y ^ 2)) + (x * y * (z ^ 2))))^2 + (1 : ℝ) * ((((-1) * (x ^ 2) * (z ^ 2)) + (x * z * (y ^ 2))))^2 + ((1 / 2) : ℝ) * (((x * z * (y ^ 2)) + ((-1) * y * z * (x ^ 2))))^2 := by positivity
      _ = ((x^2*y^2+y^2*z^2+z^2*x^2)^2) - (3*x^2*y^2*z^2*(x*y+y*z+z*x)) := by ring
  exact sub_nonneg.mp h
