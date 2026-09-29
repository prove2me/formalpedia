-- Prove2me | solution 1 for lean_workbook_plus_40426
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:36:55.147967+00:00
-- url     : https://prove2.me/submissions/e164bae1-c1f0-49b1-9bfc-9c4f794b7074

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y z : ℝ) (hx : 0 < x ∧ 0 < y ∧ 0 < z) (h : x * y + y * z + z * x = 1) :
  x * (y^2 + z^2) * (x^2 - y * z) + y * (z^2 + x^2) * (y^2 - z * x) + z * (x^2 + y^2) * (z^2 - x * y) ≥ 0 := by
  intros
  have hpos_x : (0 : ℝ) ≤ x := by first | positivity | linarith
  have hpos_y : (0 : ℝ) ≤ y := by first | positivity | linarith
  have hpos_z : (0 : ℝ) ≤ z := by first | positivity | linarith
  have h : (0 : ℝ) ≤ (x * (y^2 + z^2) * (x^2 - y * z) + y * (z^2 + x^2) * (y^2 - z * x) + z * (x^2 + y^2) * (z^2 - x * y)) - (0) := by
    calc
      0 ≤ (1 : ℝ) * (z) * (((x * z) + ((-1) * y * z)))^2 + (1 : ℝ) * (y) * (((x * y) + ((-1) * y * z)))^2 + (1 : ℝ) * (x) * (((x * y) + ((-1) * x * z)))^2 := by positivity
      _ = (x * (y^2 + z^2) * (x^2 - y * z) + y * (z^2 + x^2) * (y^2 - z * x) + z * (x^2 + y^2) * (z^2 - x * y)) - (0) := by ring
  exact sub_nonneg.mp h
