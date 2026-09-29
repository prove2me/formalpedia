-- Prove2me | solution 1 for lean_workbook_plus_38288
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:40:23.58827+00:00
-- url     : https://prove2.me/submissions/5352eb9d-5ccb-49f4-a5a0-7307da91e6e1

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℝ) (hx : x ≥ 0) : 2 * x ^ 5 - 5 * x ^ 2 + 3 ≥ 0 := by
  intros
  have hpos_x : (0 : ℝ) ≤ x := by first | positivity | linarith
  have h : (0 : ℝ) ≤ (2 * x ^ 5 - 5 * x ^ 2 + 3) - (0) := by
    calc
      0 ≤ ((1 / 3) : ℝ) * (1) * ((1 + ((-1) * x)))^2 + ((8 / 3) : ℝ) * (1) * ((1 + ((-1) * (x ^ 2))))^2 + ((2 / 3) : ℝ) * (x) * ((1 + ((-1) * (x ^ 2))))^2 + ((4 / 3) : ℝ) * (x) * ((x + ((-1) * (x ^ 2))))^2 := by positivity
      _ = (2 * x ^ 5 - 5 * x ^ 2 + 3) - (0) := by ring
  exact sub_nonneg.mp h
