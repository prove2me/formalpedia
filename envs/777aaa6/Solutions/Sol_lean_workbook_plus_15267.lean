-- Prove2me | solution 1 for lean_workbook_plus_15267
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:44:31.378599+00:00
-- url     : https://prove2.me/submissions/53c12452-1056-42c4-a5f5-cbf70cf75d82

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : 8 * (x ^ 3 + y ^ 3 + z ^ 3) ^ 2 ≥ 9 * (x ^ 2 + y * z) * (y ^ 2 + z * x) * (z ^ 2 + x * y) := by
  intros
  have hpos_x : (0 : ℝ) ≤ x := by first | positivity | linarith
  have hpos_y : (0 : ℝ) ≤ y := by first | positivity | linarith
  have hpos_z : (0 : ℝ) ≤ z := by first | positivity | linarith
  have h : (0 : ℝ) ≤ (8 * (x ^ 3 + y ^ 3 + z ^ 3) ^ 2) - (9 * (x ^ 2 + y * z) * (y ^ 2 + z * x) * (z ^ 2 + x * y)) := by
    calc
      0 ≤ (8 : ℝ) * (1) * (((x ^ 3) + ((-1) * x * y * z)))^2 + (8 : ℝ) * (1) * ((((-1) * (y ^ 3)) + (x * y * z)))^2 + (8 : ℝ) * (1) * ((((-1) * (z ^ 3)) + (x * y * z)))^2 + (7 : ℝ) * ((y * z)) * (((x ^ 2) + ((-1) * y * z)))^2 + (7 : ℝ) * ((x * z)) * ((((-1) * (y ^ 2)) + (x * z)))^2 + (7 : ℝ) * ((x * y)) * ((((-1) * (z ^ 2)) + (x * y)))^2 := by positivity
      _ = (8 * (x ^ 3 + y ^ 3 + z ^ 3) ^ 2) - (9 * (x ^ 2 + y * z) * (y ^ 2 + z * x) * (z ^ 2 + x * y)) := by ring
  exact sub_nonneg.mp h
