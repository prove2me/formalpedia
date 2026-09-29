-- Prove2me | solution 1 for lean_workbook_plus_76112
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:19:09.229136+00:00
-- url     : https://prove2.me/submissions/de4a75c1-4c01-423e-afcd-b73e528853d3

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b: ℝ) : a ^ 2 + b ^ 2 + 1 ≥ a * b + a + b := by
  intros
  have h : (0 : ℝ) ≤ (a ^ 2 + b ^ 2 + 1) - (a * b + a + b) := by
    calc
      0 ≤ ((1 / 2) : ℝ) * ((1 + ((-1) * b)))^2 + ((1 / 2) : ℝ) * ((1 + ((-1) * a)))^2 + ((1 / 2) : ℝ) * ((b + ((-1) * a)))^2 := by positivity
      _ = (a ^ 2 + b ^ 2 + 1) - (a * b + a + b) := by ring
  exact sub_nonneg.mp h
