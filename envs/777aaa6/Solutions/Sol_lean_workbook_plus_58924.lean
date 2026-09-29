-- Prove2me | solution 1 for lean_workbook_plus_58924
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:38:17.457495+00:00
-- url     : https://prove2.me/submissions/243cff07-025b-4951-95d8-ce22cdd10511

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : x^2 + 2*y^3 - y^4 ≤ (2*x^3 + 1)/3 + 2*y^3 - (4*y^3 - 1)/3 := by
  intros
  have hpos_x : (0 : ℝ) ≤ x := by first | positivity | linarith
  have h : (0 : ℝ) ≤ ((2*x^3 + 1)/3 + 2*y^3 - (4*y^3 - 1)/3) - (x^2 + 2*y^3 - y^4) := by
    calc
      0 ≤ ((1 / 3) : ℝ) * (1) * ((1 + ((-1) * x)))^2 + ((1 / 3) : ℝ) * (1) * ((1 + ((-1) * (y ^ 2))))^2 + ((2 / 3) : ℝ) * (1) * ((y + ((-1) * (y ^ 2))))^2 + ((2 / 3) : ℝ) * (x) * ((1 + ((-1) * x)))^2 := by positivity
      _ = ((2*x^3 + 1)/3 + 2*y^3 - (4*y^3 - 1)/3) - (x^2 + 2*y^3 - y^4) := by ring
  exact sub_nonneg.mp h
