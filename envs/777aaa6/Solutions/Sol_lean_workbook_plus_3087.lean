-- Prove2me | solution 1 for lean_workbook_plus_3087
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:45:08.578899+00:00
-- url     : https://prove2.me/submissions/ce3fb702-aab3-4b16-9c67-4802bcb93720

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : x ^ 4 * z ^ 2 + y ^ 4 * x ^ 2 + z ^ 4 * y ^ 2 ≥ x * y * z * (x ^ 2 * z + y ^ 2 * x + z ^ 2 * y) := by
  intros
  have hpos_x : (0 : ℝ) ≤ x := by first | positivity | linarith
  have hpos_y : (0 : ℝ) ≤ y := by first | positivity | linarith
  have h : (0 : ℝ) ≤ (x ^ 4 * z ^ 2 + y ^ 4 * x ^ 2 + z ^ 4 * y ^ 2) - (x * y * z * (x ^ 2 * z + y ^ 2 * x + z ^ 2 * y)) := by
    calc
      0 ≤ (1 : ℝ) * (1) * (((z * (x ^ 2)) + ((-1) * x * y * z)))^2 + ((1 / 2) : ℝ) * (1) * (((x * (y ^ 2)) + ((-1) * x * y * z)))^2 + ((1 / 2) : ℝ) * (1) * (((x * (y ^ 2)) + ((-1) * y * (z ^ 2))))^2 + ((1 / 2) : ℝ) * (1) * ((((-1) * y * (z ^ 2)) + (x * y * z)))^2 + (1 : ℝ) * ((x * y)) * (((x * z) + ((-1) * y * z)))^2 := by positivity
      _ = (x ^ 4 * z ^ 2 + y ^ 4 * x ^ 2 + z ^ 4 * y ^ 2) - (x * y * z * (x ^ 2 * z + y ^ 2 * x + z ^ 2 * y)) := by ring
  exact sub_nonneg.mp h
