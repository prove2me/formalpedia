-- Prove2me | solution 1 for lean_workbook_plus_11592
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:42:02.937656+00:00
-- url     : https://prove2.me/submissions/53c456c1-8438-4d21-b754-b96c650689da

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x * y + y * z + z * x)^3 ≤ 27 * ((x + y) * (y + z) * (z + x))^2 := by
  intros
  have hpos_x : (0 : ℝ) ≤ x := by first | positivity | linarith
  have hpos_y : (0 : ℝ) ≤ y := by first | positivity | linarith
  have hpos_z : (0 : ℝ) ≤ z := by first | positivity | linarith
  have h : (0 : ℝ) ≤ (27 * ((x + y) * (y + z) * (z + x))^2) - ((x * y + y * z + z * x)^3) := by
    calc
      0 ≤ ((3549 / 928) : ℝ) * (1) * (((y * (x ^ 2)) + (2 * z * (x ^ 2))))^2 + ((777 / 928) : ℝ) * (1) * (((y * (x ^ 2)) + (2 * x * (y ^ 2))))^2 + ((4899 / 232) : ℝ) * (1) * (((y * (x ^ 2)) + (2 * x * y * z)))^2 + ((567 / 464) : ℝ) * (1) * (((y * (x ^ 2)) + (2 * z * (y ^ 2))))^2 + ((1149 / 232) : ℝ) * (1) * (((z * (x ^ 2)) + (2 * x * (y ^ 2))))^2 + ((27 / 4) : ℝ) * (1) * (((z * (x ^ 2)) + (2 * x * (z ^ 2))))^2 + ((891 / 232) : ℝ) * (1) * (((x * (y ^ 2)) + (2 * z * (y ^ 2))))^2 + ((27 / 4) : ℝ) * (1) * (((z * (y ^ 2)) + (2 * y * (z ^ 2))))^2 + ((2181 / 464) : ℝ) * ((y * z)) * (((x ^ 2) + (2 * x * y)))^2 + ((15777 / 464) : ℝ) * ((y * z)) * (((x ^ 2) + (2 * x * z)))^2 + ((13 / 2) : ℝ) * ((y * z)) * (((x * z) + (2 * y * z)))^2 + ((1589 / 464) : ℝ) * ((x * z)) * (((x * y) + (2 * x * z)))^2 + ((10767 / 464) : ℝ) * ((x * z)) * (((x * y) + (2 * y * z)))^2 + ((3795 / 464) : ℝ) * ((x * z)) * (((2 * (y ^ 2)) + (x * z)))^2 + ((1913 / 464) : ℝ) * ((x * z)) * (((x * z) + (2 * y * z)))^2 + ((687 / 116) : ℝ) * ((x * z)) * (((y ^ 2) + (2 * y * z)))^2 + ((539 / 232) : ℝ) * ((x * y)) * (((x * y) + (2 * x * z)))^2 + ((981 / 29) : ℝ) * ((x * y)) * (((x * y) + (2 * y * z)))^2 + ((27 / 2) : ℝ) * ((x * y)) * (((2 * (z ^ 2)) + (x * y)))^2 := by positivity
      _ = (27 * ((x + y) * (y + z) * (z + x))^2) - ((x * y + y * z + z * x)^3) := by ring
  exact sub_nonneg.mp h
