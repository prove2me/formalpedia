-- Prove2me | solution 1 for lean_workbook_plus_38355
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:34:44.392817+00:00
-- url     : https://prove2.me/submissions/a8b0da9c-41c4-435a-944c-40cfd3565657

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : 2 * c ^ 5 + a ^ 3 * (b + c) ^ 2 ≥ 2 * a * c * (c ^ 3 + a * b * c + a ^ 2 * b) := by
  intros
  have hpos_a : (0 : ℝ) ≤ a := by first | positivity | linarith
  have hpos_c : (0 : ℝ) ≤ c := by first | positivity | linarith
  have h : (0 : ℝ) ≤ (2 * c ^ 5 + a ^ 3 * (b + c) ^ 2) - (2 * a * c * (c ^ 3 + a * b * c + a ^ 2 * b)) := by
    calc
      0 ≤ (2 : ℝ) * (c) * ((((-1) * (c ^ 2)) + (a * c)))^2 + (1 : ℝ) * (a) * ((((-1) * (c ^ 2)) + (a * b)))^2 + (1 : ℝ) * (a) * ((((-1) * (c ^ 2)) + (a * c)))^2 := by positivity
      _ = (2 * c ^ 5 + a ^ 3 * (b + c) ^ 2) - (2 * a * c * (c ^ 3 + a * b * c + a ^ 2 * b)) := by ring
  exact sub_nonneg.mp h
