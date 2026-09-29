-- Prove2me | solution 1 for lean_workbook_plus_29928
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:27:34.431148+00:00
-- url     : https://prove2.me/submissions/61482660-4c40-4bd3-9ca7-b1414ba8c03d

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution {x y z : ℝ} (hx : x > 0 ∧ y > 0 ∧ z > 0) (hxy : x + y > z) (hxz : x + z > y) (hyz : y + z > x) :  (y - z) ^ 2 * (13 * x ^ 3 + 34 * x ^ 2 * y + 36 * x ^ 2 * z + y * z ^ 2) + (x - z) ^ 2 * (x ^ 2 * y + 3 * x ^ 2 * z + 5 * y ^ 2 * z + 9 * x * z ^ 2) + (x - y) ^ 4 * z + (x - y) ^ 2 * (9 * x * y ^ 2 + 3 * x ^ 2 * y) + 2 * (x * y - 2 * x * z + y * z) ^ 2 * y ≥ 0 := by
  intros
  have hpos_x : (0 : ℝ) ≤ x := by first | positivity | linarith
  have hpos_y : (0 : ℝ) ≤ y := by first | positivity | linarith
  have hpos_z : (0 : ℝ) ≤ z := by first | positivity | linarith
  have h : (0 : ℝ) ≤ ((y - z) ^ 2 * (13 * x ^ 3 + 34 * x ^ 2 * y + 36 * x ^ 2 * z + y * z ^ 2) + (x - z) ^ 2 * (x ^ 2 * y + 3 * x ^ 2 * z + 5 * y ^ 2 * z + 9 * x * z ^ 2) + (x - y) ^ 4 * z + (x - y) ^ 2 * (9 * x * y ^ 2 + 3 * x ^ 2 * y) + 2 * (x * y - 2 * x * z + y * z) ^ 2 * y) - (0) := by
    calc
      0 ≤ (1 : ℝ) * (z) * (((x ^ 2) + ((-1) * x * z)))^2 + (3 : ℝ) * (z) * (((x ^ 2) + ((-1) * y * z)))^2 + (19 : ℝ) * (z) * (((x * y) + ((-1) * x * z)))^2 + (1 : ℝ) * (z) * ((((-1) * (y ^ 2)) + (x * z)))^2 + (1 : ℝ) * (y) * (((x ^ 2) + ((-1) * x * y)))^2 + (3 : ℝ) * (y) * (((x ^ 2) + ((-1) * y * z)))^2 + (19 : ℝ) * (y) * (((x * y) + ((-1) * x * z)))^2 + (1 : ℝ) * (y) * ((((-1) * (z ^ 2)) + (x * y)))^2 + (16 : ℝ) * (x) * (((x * y) + ((-1) * x * z)))^2 + (2 : ℝ) * (x) * ((((-1) * (z ^ 2)) + (x * y)))^2 + (2 : ℝ) * (x) * ((((-1) * (y ^ 2)) + (x * z)))^2 + (7 : ℝ) * (x) * (((y ^ 2) + ((-1) * (z ^ 2))))^2 := by positivity
      _ = ((y - z) ^ 2 * (13 * x ^ 3 + 34 * x ^ 2 * y + 36 * x ^ 2 * z + y * z ^ 2) + (x - z) ^ 2 * (x ^ 2 * y + 3 * x ^ 2 * z + 5 * y ^ 2 * z + 9 * x * z ^ 2) + (x - y) ^ 4 * z + (x - y) ^ 2 * (9 * x * y ^ 2 + 3 * x ^ 2 * y) + 2 * (x * y - 2 * x * z + y * z) ^ 2 * y) - (0) := by ring
  exact sub_nonneg.mp h
