-- Prove2me | solution 1 for lean_workbook_plus_5613
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:45:24.93629+00:00
-- url     : https://prove2.me/submissions/e80f4e60-2c72-4da4-aac9-d6cc6df9c4cf

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℝ) (hx : 0 < x ∧ x < 1) :
  x^8 + x^7 + x^6 - x^5 + x^3 - x^2 + 1 ≥ 0 := by
  intros
  have hpos_x : (0 : ℝ) ≤ x := by first | positivity | linarith
  have h : (0 : ℝ) ≤ (x^8 + x^7 + x^6 - x^5 + x^3 - x^2 + 1) - (0) := by
    calc
      0 ≤ ((1 / 4) : ℝ) * (1) * ((1 + ((-2) * (x ^ 2))))^2 + ((7 / 32) : ℝ) * (1) * ((1 + (2 * (x ^ 3))))^2 + ((1 / 32) : ℝ) * (1) * ((1 + ((-2) * (x ^ 3))))^2 + ((1 / 3) : ℝ) * (1) * ((1 + ((-1) * (x ^ 4))))^2 + ((1 / 24) : ℝ) * (1) * ((1 + (2 * (x ^ 4))))^2 + ((1 / 8) : ℝ) * (1) * ((1 + ((-2) * (x ^ 4))))^2 + ((1 / 4) : ℝ) * (x) * ((x + ((-2) * (x ^ 3))))^2 := by positivity
      _ = (x^8 + x^7 + x^6 - x^5 + x^3 - x^2 + 1) - (0) := by ring
  exact sub_nonneg.mp h
