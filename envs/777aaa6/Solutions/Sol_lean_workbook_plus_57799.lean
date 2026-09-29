-- Prove2me | solution 1 for lean_workbook_plus_57799
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:40:30.709744+00:00
-- url     : https://prove2.me/submissions/2d3e88e6-dc55-40de-8a7f-e02f4d1e2513

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b : ℝ) : (1 + a ^ 2) * (1 + b ^ 2) ≥ (a + b) * (1 + a * b) := by
  intros
  have h : (0 : ℝ) ≤ ((1 + a ^ 2) * (1 + b ^ 2)) - ((a + b) * (1 + a * b)) := by
    calc
      0 ≤ ((1 / 2) : ℝ) * ((1 + ((-1) * b)))^2 + ((1 / 2) : ℝ) * ((1 + ((-1) * a)))^2 + ((1 / 2) : ℝ) * ((b + ((-1) * a * b)))^2 + ((1 / 2) : ℝ) * ((a + ((-1) * a * b)))^2 := by positivity
      _ = ((1 + a ^ 2) * (1 + b ^ 2)) - ((a + b) * (1 + a * b)) := by ring
  exact sub_nonneg.mp h
