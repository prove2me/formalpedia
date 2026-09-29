-- Prove2me | solution 1 for lean_workbook_plus_31271
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:36:52.589622+00:00
-- url     : https://prove2.me/submissions/2a855745-5c0b-477f-85ab-14a9e1a38aa8

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℝ) (hx : 0 < x) : (x + 1) * (x + 2) * (x + 5) ≥ 36 * x := by
  intros
  have hpos_x : (0 : ℝ) ≤ x := by first | positivity | linarith
  have h : (0 : ℝ) ≤ ((x + 1) * (x + 2) * (x + 5)) - (36 * x) := by
    calc
      0 ≤ (10 : ℝ) * (1) * ((1 + ((-1) * x)))^2 + (1 : ℝ) * (x) * ((1 + ((-1) * x)))^2 := by positivity
      _ = ((x + 1) * (x + 2) * (x + 5)) - (36 * x) := by ring
  exact sub_nonneg.mp h
