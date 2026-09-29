-- Prove2me | solution 1 for lean_workbook_plus_18674
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:37:55.97622+00:00
-- url     : https://prove2.me/submissions/5c724100-be6f-4c29-aa4c-cec6ebf3ff89

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : x^6 + y^6 + 4 * (x^3 * y^3) ≥ 3 * (y^4 * x^2 + x^4 * y^2) := by
  intros
  have hpos_x : (0 : ℝ) ≤ x := by first | positivity | linarith
  have hpos_y : (0 : ℝ) ≤ y := by first | positivity | linarith
  have h : (0 : ℝ) ≤ (x^6 + y^6 + 4 * (x^3 * y^3)) - (3 * (y^4 * x^2 + x^4 * y^2)) := by
    calc
      0 ≤ (1 : ℝ) * (1) * ((((-1) * (x ^ 3)) + (y * (x ^ 2))))^2 + (1 : ℝ) * (1) * ((((-1) * (y ^ 3)) + (x * (y ^ 2))))^2 + (2 : ℝ) * ((x * y)) * (((x ^ 2) + ((-1) * x * y)))^2 + (2 : ℝ) * ((x * y)) * ((((-1) * (y ^ 2)) + (x * y)))^2 := by positivity
      _ = (x^6 + y^6 + 4 * (x^3 * y^3)) - (3 * (y^4 * x^2 + x^4 * y^2)) := by ring
  exact sub_nonneg.mp h
