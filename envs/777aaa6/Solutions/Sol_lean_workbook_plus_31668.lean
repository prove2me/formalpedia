-- Prove2me | solution 1 for lean_workbook_plus_31668
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:44:38.736715+00:00
-- url     : https://prove2.me/submissions/a495369f-60e7-4944-88f2-153c00d7f913

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + y + z) ^ 2 * (x * y + y * z + z * x) ^ 2 ≤ 3 * (y ^ 2 + y * z + z ^ 2) * (z ^ 2 + z * x + x ^ 2) * (x ^ 2 + x * y + y ^ 2) := by
  intros
  have hpos_x : (0 : ℝ) ≤ x := by first | positivity | linarith
  have hpos_y : (0 : ℝ) ≤ y := by first | positivity | linarith
  have hpos_z : (0 : ℝ) ≤ z := by first | positivity | linarith
  have h : (0 : ℝ) ≤ (3 * (y ^ 2 + y * z + z ^ 2) * (z ^ 2 + z * x + x ^ 2) * (x ^ 2 + x * y + y ^ 2)) - ((x + y + z) ^ 2 * (x * y + y * z + z * x) ^ 2) := by
    calc
      0 ≤ (1 : ℝ) * (1) * (((y * (x ^ 2)) + ((-1) * x * (z ^ 2))))^2 + (1 : ℝ) * (1) * (((y * (x ^ 2)) + ((-1) * z * (y ^ 2))))^2 + (1 : ℝ) * (1) * (((z * (x ^ 2)) + ((-1) * x * (y ^ 2))))^2 + (1 : ℝ) * (1) * (((z * (x ^ 2)) + ((-1) * y * (z ^ 2))))^2 + (1 : ℝ) * (1) * (((x * (y ^ 2)) + ((-1) * y * (z ^ 2))))^2 + (1 : ℝ) * (1) * (((x * (z ^ 2)) + ((-1) * z * (y ^ 2))))^2 + (1 : ℝ) * ((y * z)) * (((x ^ 2) + ((-1) * y * z)))^2 + (1 : ℝ) * ((x * z)) * ((((-1) * (y ^ 2)) + (x * z)))^2 + (1 : ℝ) * ((x * y)) * ((((-1) * (z ^ 2)) + (x * y)))^2 := by positivity
      _ = (3 * (y ^ 2 + y * z + z ^ 2) * (z ^ 2 + z * x + x ^ 2) * (x ^ 2 + x * y + y ^ 2)) - ((x + y + z) ^ 2 * (x * y + y * z + z * x) ^ 2) := by ring
  exact sub_nonneg.mp h
