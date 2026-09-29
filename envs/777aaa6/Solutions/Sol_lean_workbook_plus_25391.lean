-- Prove2me | solution 1 for lean_workbook_plus_25391
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:41:34.577076+00:00
-- url     : https://prove2.me/submissions/57415626-a5d3-4dc8-9366-f33228e69953

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) : (x * y + x * z + y * z) * (x * y ^ 2 + y * z ^ 2 + x ^ 2 * z) - (x + y + z) ^ 2 * x * y * z ≥ 0 := by
  intros
  have hpos_x : (0 : ℝ) ≤ x := by first | positivity | linarith
  have hpos_y : (0 : ℝ) ≤ y := by first | positivity | linarith
  have hpos_z : (0 : ℝ) ≤ z := by first | positivity | linarith
  have h : (0 : ℝ) ≤ ((x * y + x * z + y * z) * (x * y ^ 2 + y * z ^ 2 + x ^ 2 * z) - (x + y + z) ^ 2 * x * y * z) - (0) := by
    calc
      0 ≤ (1 : ℝ) * (z) * (((x * y) + ((-1) * y * z)))^2 + (1 : ℝ) * (y) * (((x * y) + ((-1) * x * z)))^2 + (1 : ℝ) * (x) * (((x * z) + ((-1) * y * z)))^2 := by positivity
      _ = ((x * y + x * z + y * z) * (x * y ^ 2 + y * z ^ 2 + x ^ 2 * z) - (x + y + z) ^ 2 * x * y * z) - (0) := by ring
  exact sub_nonneg.mp h
