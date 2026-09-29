-- Prove2me | solution 1 for lean_workbook_plus_32407
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:43:24.772265+00:00
-- url     : https://prove2.me/submissions/996b5aea-b5c2-458e-8351-5a5183229187

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 → 9 * (a^3 + b^3 + c^3) ≥ (a + b + c)^3 := by
  intro a b c
  intros
  have hpos_a : (0 : ℝ) ≤ a := by first | positivity | linarith
  have hpos_b : (0 : ℝ) ≤ b := by first | positivity | linarith
  have hpos_c : (0 : ℝ) ≤ c := by first | positivity | linarith
  have h : (0 : ℝ) ≤ (9 * (a^3 + b^3 + c^3)) - ((a + b + c)^3) := by
    calc
      0 ≤ (3 : ℝ) * (c) * ((a + ((-1) * c)))^2 + (5 : ℝ) * (c) * ((b + ((-1) * c)))^2 + (4 : ℝ) * (b) * ((a + ((-1) * b)))^2 + (3 : ℝ) * (b) * ((a + ((-1) * c)))^2 + (4 : ℝ) * (b) * ((b + ((-1) * c)))^2 + (5 : ℝ) * (a) * ((a + ((-1) * b)))^2 + (3 : ℝ) * (a) * ((a + ((-1) * c)))^2 := by positivity
      _ = (9 * (a^3 + b^3 + c^3)) - ((a + b + c)^3) := by ring
  exact sub_nonneg.mp h
