-- Prove2me | solution 1 for lean_workbook_plus_75540
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:44:09.281551+00:00
-- url     : https://prove2.me/submissions/39b1999f-d330-47c3-8714-6578d2356db5

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a : ℝ) (ha : 0 < a) :
  16 * (a + 2)^4 * (2 * a + 1) ≥ 243 * (a + 1)^4 := by
  intros
  have hpos_a : (0 : ℝ) ≤ a := by first | positivity | linarith
  have h : (0 : ℝ) ≤ (16 * (a + 2)^4 * (2 * a + 1)) - (243 * (a + 1)^4) := by
    calc
      0 ≤ (13 : ℝ) * (1) * ((1 + ((-1) * (a ^ 2))))^2 + (16 : ℝ) * (1) * ((a + ((-1) * (a ^ 2))))^2 + (20 : ℝ) * (a) * ((1 + ((-1) * a)))^2 + (32 : ℝ) * (a) * ((1 + ((-1) * (a ^ 2))))^2 := by positivity
      _ = (16 * (a + 2)^4 * (2 * a + 1)) - (243 * (a + 1)^4) := by ring
  exact sub_nonneg.mp h
