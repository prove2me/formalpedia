-- Prove2me | solution 1 for lean_workbook_plus_8232
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:43:39.888347+00:00
-- url     : https://prove2.me/submissions/bf1f4162-c79a-4ed6-a5e7-a5927add94aa

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : x^2*y^3 + x^2*z^3 + y^2*x^3 + y^2*z^3 + z^2*x^3 + z^2*y^3 ≤ x*y^4 + x*z^4 + y*x^4 + y*z^4 + z*x^4 + z*y^4 := by
  intros
  have hpos_x : (0 : ℝ) ≤ x := by first | positivity | linarith
  have hpos_y : (0 : ℝ) ≤ y := by first | positivity | linarith
  have hpos_z : (0 : ℝ) ≤ z := by first | positivity | linarith
  have h : (0 : ℝ) ≤ (x*y^4 + x*z^4 + y*x^4 + y*z^4 + z*x^4 + z*y^4) - (x^2*y^3 + x^2*z^3 + y^2*x^3 + y^2*z^3 + z^2*x^3 + z^2*y^3) := by
    calc
      0 ≤ (1 : ℝ) * (z) * (((x ^ 2) + ((-1) * x * z)))^2 + (1 : ℝ) * (z) * (((y ^ 2) + ((-1) * y * z)))^2 + (1 : ℝ) * (y) * (((x ^ 2) + ((-1) * x * y)))^2 + (1 : ℝ) * (y) * ((((-1) * (z ^ 2)) + (y * z)))^2 + (1 : ℝ) * (x) * ((((-1) * (y ^ 2)) + (x * y)))^2 + (1 : ℝ) * (x) * ((((-1) * (z ^ 2)) + (x * z)))^2 := by positivity
      _ = (x*y^4 + x*z^4 + y*x^4 + y*z^4 + z*x^4 + z*y^4) - (x^2*y^3 + x^2*z^3 + y^2*x^3 + y^2*z^3 + z^2*x^3 + z^2*y^3) := by ring
  exact sub_nonneg.mp h
