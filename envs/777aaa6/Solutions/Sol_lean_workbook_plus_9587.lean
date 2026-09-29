-- Prove2me | solution 1 for lean_workbook_plus_9587
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:21:25.076702+00:00
-- url     : https://prove2.me/submissions/76e524a6-84d3-4e1f-9e1e-b786c92c66e8

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y z : ℝ) : x ^ 4 * y ^ 2 * z ^ 2 - x ^ 3 * y ^ 3 * z ^ 2 - y ^ 3 * z ^ 3 * x ^ 2 + y ^ 2 * z ^ 4 * x ^ 2 + x ^ 2 * y ^ 4 * z ^ 2 - x ^ 3 * y ^ 2 * z ^ 3 ≥ 0 := by
  intros
  have h : (0 : ℝ) ≤ (x ^ 4 * y ^ 2 * z ^ 2 - x ^ 3 * y ^ 3 * z ^ 2 - y ^ 3 * z ^ 3 * x ^ 2 + y ^ 2 * z ^ 4 * x ^ 2 + x ^ 2 * y ^ 4 * z ^ 2 - x ^ 3 * y ^ 2 * z ^ 3) - (0) := by
    calc
      0 ≤ ((1 / 2) : ℝ) * (((x * y * (z ^ 2)) + ((-1) * x * z * (y ^ 2))))^2 + ((1 / 2) : ℝ) * (((x * y * (z ^ 2)) + ((-1) * y * z * (x ^ 2))))^2 + ((1 / 2) : ℝ) * (((x * z * (y ^ 2)) + ((-1) * y * z * (x ^ 2))))^2 := by positivity
      _ = (x ^ 4 * y ^ 2 * z ^ 2 - x ^ 3 * y ^ 3 * z ^ 2 - y ^ 3 * z ^ 3 * x ^ 2 + y ^ 2 * z ^ 4 * x ^ 2 + x ^ 2 * y ^ 4 * z ^ 2 - x ^ 3 * y ^ 2 * z ^ 3) - (0) := by ring
  exact sub_nonneg.mp h
