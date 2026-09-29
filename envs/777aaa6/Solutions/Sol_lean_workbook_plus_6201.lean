-- Prove2me | solution 1 for lean_workbook_plus_6201
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:15:06.309363+00:00
-- url     : https://prove2.me/submissions/8412400c-a281-402f-9244-461494eadf60

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b : ℝ) : 2 * (a ^ 2 + 1) * (b ^ 2 + 1) ≥ (a + 1) * (b + 1) * (a * b + 1) := by
  intros
  have h : (0 : ℝ) ≤ (2 * (a ^ 2 + 1) * (b ^ 2 + 1)) - ((a + 1) * (b + 1) * (a * b + 1)) := by
    calc
      0 ≤ ((1 / 2) : ℝ) * ((1 + ((-1) * b)))^2 + ((1 / 2) : ℝ) * ((1 + ((-1) * a)))^2 + (1 : ℝ) * ((b + ((-1) * a)))^2 + ((1 / 2) : ℝ) * ((b + ((-1) * a * b)))^2 + ((1 / 2) : ℝ) * ((a + ((-1) * a * b)))^2 := by positivity
      _ = (2 * (a ^ 2 + 1) * (b ^ 2 + 1)) - ((a + 1) * (b + 1) * (a * b + 1)) := by ring
  exact sub_nonneg.mp h
