-- Prove2me | solution 1 for lean_workbook_plus_70638
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:43:17.473483+00:00
-- url     : https://prove2.me/submissions/463d5caf-cb03-4e1c-b6e2-72e74cb13c04

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) : (a^3 + b^6) / 2 ≥ 3 * a * b^2 - 4 := by
  intros
  have hpos_a : (0 : ℝ) ≤ a := by first | positivity | linarith
  have h : (0 : ℝ) ≤ ((a^3 + b^6) / 2) - (3 * a * b^2 - 4) := by
    calc
      0 ≤ (4 : ℝ) * (1) * ((1 + ((-1 / 2) * (b ^ 2))))^2 + ((3 / 4) : ℝ) * (1) * ((((-2) * b) + (a * b)))^2 + ((1 / 4) : ℝ) * (1) * ((((-1) * (b ^ 3)) + (a * b)))^2 + (1 : ℝ) * (1) * ((b + ((-1 / 2) * (b ^ 3))))^2 + ((1 / 2) : ℝ) * (a) * ((a + ((-1) * (b ^ 2))))^2 := by positivity
      _ = ((a^3 + b^6) / 2) - (3 * a * b^2 - 4) := by ring
  exact sub_nonneg.mp h
