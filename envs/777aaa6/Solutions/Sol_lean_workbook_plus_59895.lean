-- Prove2me | solution 1 for lean_workbook_plus_59895
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:37:52.145245+00:00
-- url     : https://prove2.me/submissions/36393b21-2461-4635-9825-776639d1ed0e

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) : (a^2 + b + 3/4) * (b^2 + a + 3/4) ≥ (2*a + 1/2) * (2*b + 1/2) := by
  intros
  have hpos_a : (0 : ℝ) ≤ a := by first | positivity | linarith
  have hpos_b : (0 : ℝ) ≤ b := by first | positivity | linarith
  have h : (0 : ℝ) ≤ ((a^2 + b + 3/4) * (b^2 + a + 3/4)) - ((2*a + 1/2) * (2*b + 1/2)) := by
    calc
      0 ≤ ((1 / 8) : ℝ) * (1) * ((1 + ((-2) * a)))^2 + ((3 / 16) : ℝ) * (1) * ((1 + ((-2) * b)))^2 + ((1 / 4) : ℝ) * (1) * ((a + ((-2) * a * b)))^2 + (1 : ℝ) * (1) * ((a + ((-1) * b)))^2 + ((1 / 4) : ℝ) * (b) * ((1 + ((-2) * a)))^2 + ((1 / 4) : ℝ) * (b) * ((1 + ((-2) * b)))^2 + ((1 / 4) : ℝ) * (a) * ((1 + ((-2) * a)))^2 := by positivity
      _ = ((a^2 + b + 3/4) * (b^2 + a + 3/4)) - ((2*a + 1/2) * (2*b + 1/2)) := by ring
  exact sub_nonneg.mp h
