-- Prove2me | solution 1 for lean_workbook_plus_18867
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:40:01.920696+00:00
-- url     : https://prove2.me/submissions/a53c5719-113d-4bb5-a1a0-87bef4450673

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution {x y z : ℝ} (hx : x > 0) (hy : y > 0) (hz : z > 0) : 2 * (x^2 + 5 * x * y + y^2 + 5 * z * x + 5 * z * y + z^2) * (x^2 - x * y + y^2 - z * x - z * y + z^2) ≥ 0 := by
  intros
  have hpos_x : (0 : ℝ) ≤ x := by first | positivity | linarith
  have hpos_y : (0 : ℝ) ≤ y := by first | positivity | linarith
  have hpos_z : (0 : ℝ) ≤ z := by first | positivity | linarith
  have h : (0 : ℝ) ≤ (2 * (x^2 + 5 * x * y + y^2 + 5 * z * x + 5 * z * y + z^2) * (x^2 - x * y + y^2 - z * x - z * y + z^2)) - (0) := by
    calc
      0 ≤ (2 : ℝ) * (1) * (((x ^ 2) + ((-1) * y * z)))^2 + (4 : ℝ) * (1) * (((x * y) + ((-1) * x * z)))^2 + (4 : ℝ) * (1) * (((x * y) + ((-1) * y * z)))^2 + (2 : ℝ) * (1) * ((((-1) * (z ^ 2)) + (x * y)))^2 + (2 : ℝ) * (1) * ((((-1) * (y ^ 2)) + (x * z)))^2 + (4 : ℝ) * (1) * (((x * z) + ((-1) * y * z)))^2 + (8 : ℝ) * ((y * z)) * ((y + ((-1) * z)))^2 + (8 : ℝ) * ((x * z)) * ((x + ((-1) * z)))^2 + (8 : ℝ) * ((x * y)) * ((x + ((-1) * y)))^2 := by positivity
      _ = (2 * (x^2 + 5 * x * y + y^2 + 5 * z * x + 5 * z * y + z^2) * (x^2 - x * y + y^2 - z * x - z * y + z^2)) - (0) := by ring
  exact sub_nonneg.mp h
