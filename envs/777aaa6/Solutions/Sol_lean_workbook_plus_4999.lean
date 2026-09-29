-- Prove2me | solution 1 for lean_workbook_plus_4999
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:37:35.0611+00:00
-- url     : https://prove2.me/submissions/224747d0-238d-455e-9b37-539328f0406c

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (a^2 + b + 3 / 4) * (b^2 + a + 3 / 4) ≥ (2 * a + 1 / 2) * (2 * b + 1 / 2) := by
  intros
  have hpos_a : (0 : ℝ) ≤ a := by first | positivity | linarith
  have hpos_b : (0 : ℝ) ≤ b := by first | positivity | linarith
  have h : (0 : ℝ) ≤ ((a^2 + b + 3 / 4) * (b^2 + a + 3 / 4)) - ((2 * a + 1 / 2) * (2 * b + 1 / 2)) := by
    calc
      0 ≤ ((1 / 8) : ℝ) * (1) * ((1 + ((-2) * a)))^2 + ((3 / 16) : ℝ) * (1) * ((1 + ((-2) * b)))^2 + ((1 / 4) : ℝ) * (1) * ((a + ((-2) * a * b)))^2 + (1 : ℝ) * (1) * ((a + ((-1) * b)))^2 + ((1 / 4) : ℝ) * (b) * ((1 + ((-2) * a)))^2 + ((1 / 4) : ℝ) * (b) * ((1 + ((-2) * b)))^2 + ((1 / 4) : ℝ) * (a) * ((1 + ((-2) * a)))^2 := by positivity
      _ = ((a^2 + b + 3 / 4) * (b^2 + a + 3 / 4)) - ((2 * a + 1 / 2) * (2 * b + 1 / 2)) := by ring
  exact sub_nonneg.mp h
