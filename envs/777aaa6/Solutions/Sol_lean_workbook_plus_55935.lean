-- Prove2me | solution 1 for lean_workbook_plus_55935
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:45:01.004116+00:00
-- url     : https://prove2.me/submissions/1e12c47f-8d56-4bd4-9fd6-495b41974954

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x * y + z * x + y * z) * (x^2 * y + y^2 * z + z^2 * x) ≥ (x + y + z)^2 * x * y * z := by
  intros
  have hpos_x : (0 : ℝ) ≤ x := by first | positivity | linarith
  have hpos_y : (0 : ℝ) ≤ y := by first | positivity | linarith
  have hpos_z : (0 : ℝ) ≤ z := by first | positivity | linarith
  have h : (0 : ℝ) ≤ ((x * y + z * x + y * z) * (x^2 * y + y^2 * z + z^2 * x)) - ((x + y + z)^2 * x * y * z) := by
    calc
      0 ≤ (1 : ℝ) * (z) * (((x * y) + ((-1) * x * z)))^2 + (1 : ℝ) * (y) * (((x * z) + ((-1) * y * z)))^2 + (1 : ℝ) * (x) * (((x * y) + ((-1) * y * z)))^2 := by positivity
      _ = ((x * y + z * x + y * z) * (x^2 * y + y^2 * z + z^2 * x)) - ((x + y + z)^2 * x * y * z) := by ring
  exact sub_nonneg.mp h
