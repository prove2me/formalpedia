-- Prove2me | solution 1 for lean_workbook_plus_55337
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:39:04.854888+00:00
-- url     : https://prove2.me/submissions/2667890f-9c99-44c0-bd40-34523293e6e2

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a : ℝ) (h : a ≥ 0) : 2 * a ^ 4 + a ≥ 3 * a ^ 3 := by
  intros
  have hpos_a : (0 : ℝ) ≤ a := by first | positivity | linarith
  have h : (0 : ℝ) ≤ (2 * a ^ 4 + a) - (3 * a ^ 3) := by
    calc
      0 ≤ (2 : ℝ) * (1) * ((a + ((-1) * (a ^ 2))))^2 + (1 : ℝ) * (a) * ((1 + ((-1) * a)))^2 := by positivity
      _ = (2 * a ^ 4 + a) - (3 * a ^ 3) := by ring
  exact sub_nonneg.mp h
