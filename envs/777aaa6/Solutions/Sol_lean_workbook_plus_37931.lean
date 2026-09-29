-- Prove2me | solution 1 for lean_workbook_plus_37931
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:37:48.138388+00:00
-- url     : https://prove2.me/submissions/cfe1337c-3419-48b2-a33d-9e0f4b2fd618

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : x ^ 3 * z ^ 2 + y ^ 3 * x ^ 2 + z ^ 3 * y ^ 2 ≥ z ^ 2 * x ^ 2 * y + x ^ 2 * y ^ 2 * z + z ^ 2 * y ^ 2 * x := by
  intros
  have hpos_x : (0 : ℝ) ≤ x := by first | positivity | linarith
  have hpos_y : (0 : ℝ) ≤ y := by first | positivity | linarith
  have hpos_z : (0 : ℝ) ≤ z := by first | positivity | linarith
  have h : (0 : ℝ) ≤ (x ^ 3 * z ^ 2 + y ^ 3 * x ^ 2 + z ^ 3 * y ^ 2) - (z ^ 2 * x ^ 2 * y + x ^ 2 * y ^ 2 * z + z ^ 2 * y ^ 2 * x) := by
    calc
      0 ≤ (1 : ℝ) * (z) * (((x * y) + ((-1) * y * z)))^2 + (1 : ℝ) * (y) * (((x * y) + ((-1) * x * z)))^2 + (1 : ℝ) * (x) * (((x * z) + ((-1) * y * z)))^2 := by positivity
      _ = (x ^ 3 * z ^ 2 + y ^ 3 * x ^ 2 + z ^ 3 * y ^ 2) - (z ^ 2 * x ^ 2 * y + x ^ 2 * y ^ 2 * z + z ^ 2 * y ^ 2 * x) := by ring
  exact sub_nonneg.mp h
