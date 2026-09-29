-- Prove2me | solution 1 for lean_workbook_plus_30544
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:30:40.591503+00:00
-- url     : https://prove2.me/submissions/a267e8e5-d641-4743-a350-fa4c2f63e426

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : 3 * (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) * (a * b ^ 2 + b * c ^ 2 + c * a ^ 2) ≤ (a ^ 2 + b ^ 2 + c ^ 2) ^ 3 := by
  intros
  have h : (0 : ℝ) ≤ ((a ^ 2 + b ^ 2 + c ^ 2) ^ 3) - (3 * (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) * (a * b ^ 2 + b * c ^ 2 + c * a ^ 2)) := by
    calc
      0 ≤ ((1 / 2) : ℝ) * (((c ^ 3) + ((-1) * (b ^ 3))))^2 + ((1 / 2) : ℝ) * (((c ^ 3) + ((-1) * (a ^ 3))))^2 + (1 : ℝ) * (((b * (c ^ 2)) + ((-1) * c * (b ^ 2))))^2 + ((3 / 2) : ℝ) * (((b * (c ^ 2)) + ((-1) * a * (c ^ 2))))^2 + ((1 / 2) : ℝ) * (((b * (c ^ 2)) + ((-1) * b * (a ^ 2))))^2 + ((3 / 2) : ℝ) * (((c * (b ^ 2)) + ((-1) * a * (b ^ 2))))^2 + ((1 / 2) : ℝ) * (((c * (b ^ 2)) + ((-1) * c * (a ^ 2))))^2 + ((1 / 2) : ℝ) * (((b ^ 3) + ((-1) * (a ^ 3))))^2 + ((1 / 2) : ℝ) * (((a * (c ^ 2)) + ((-1) * a * (b ^ 2))))^2 + (1 : ℝ) * (((a * (c ^ 2)) + ((-1) * c * (a ^ 2))))^2 + (1 : ℝ) * (((a * (b ^ 2)) + ((-1) * b * (a ^ 2))))^2 + ((3 / 2) : ℝ) * (((c * (a ^ 2)) + ((-1) * b * (a ^ 2))))^2 := by positivity
      _ = ((a ^ 2 + b ^ 2 + c ^ 2) ^ 3) - (3 * (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) * (a * b ^ 2 + b * c ^ 2 + c * a ^ 2)) := by ring
  exact sub_nonneg.mp h
