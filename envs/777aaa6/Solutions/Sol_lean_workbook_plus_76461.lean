-- Prove2me | solution 1 for lean_workbook_plus_76461
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:21:11.274799+00:00
-- url     : https://prove2.me/submissions/bbb264d8-3752-4c6f-8d3f-9eca182861de

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) : (a * b + b * c + c * a - 1) ≤ (a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1) := by
  intros
  have h : (0 : ℝ) ≤ ((a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1)) - ((a * b + b * c + c * a - 1)) := by
    calc
      0 ≤ ((1 / 8) : ℝ) * ((1 + (2 * c)))^2 + ((1 / 8) : ℝ) * ((1 + ((-2) * c)))^2 + ((1 / 3) : ℝ) * ((1 + ((-1) * b)))^2 + ((1 / 6) : ℝ) * ((1 + (2 * b)))^2 + ((1 / 4) : ℝ) * ((1 + ((-2) * b * c)))^2 + ((1 / 8) : ℝ) * ((1 + (2 * a)))^2 + ((1 / 8) : ℝ) * ((1 + ((-2) * a)))^2 + ((1 / 4) : ℝ) * ((1 + ((-2) * a * c)))^2 + ((1 / 4) : ℝ) * ((1 + ((-2) * a * b)))^2 + ((1 / 8) : ℝ) * ((1 + (2 * a * b * c)))^2 + ((1 / 8) : ℝ) * ((1 + ((-2) * a * b * c)))^2 := by positivity
      _ = ((a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1)) - ((a * b + b * c + c * a - 1)) := by ring
  exact sub_nonneg.mp h
