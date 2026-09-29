-- Prove2me | solution 1 for lean_workbook_plus_57756
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:44:02.812184+00:00
-- url     : https://prove2.me/submissions/733cdb7f-9ceb-49f3-bbbd-6646c9946aba

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^5 + b^5 + c^5 ≥ a * b * c * (a^2 + b^2 + c^2 + (2 / 3) * (a - b)^2) := by
  intros
  have hpos_a : (0 : ℝ) ≤ a := by first | positivity | linarith
  have hpos_b : (0 : ℝ) ≤ b := by first | positivity | linarith
  have hpos_c : (0 : ℝ) ≤ c := by first | positivity | linarith
  have h : (0 : ℝ) ≤ (a^5 + b^5 + c^5) - (a * b * c * (a^2 + b^2 + c^2 + (2 / 3) * (a - b)^2)) := by
    calc
      0 ≤ ((2 / 9) : ℝ) * (c) * (((a ^ 2) + ((-1) * (c ^ 2))))^2 + ((5 / 12) : ℝ) * (c) * (((a * b) + ((-1) * a * c)))^2 + ((5 / 12) : ℝ) * (c) * (((a * b) + ((-1) * b * c)))^2 + ((1 / 2) : ℝ) * (c) * ((((-1) * (c ^ 2)) + (a * b)))^2 + ((1 / 36) : ℝ) * (c) * ((((-1) * (c ^ 2)) + (a * c)))^2 + ((2 / 9) : ℝ) * (c) * (((b ^ 2) + ((-1) * (c ^ 2))))^2 + ((1 / 36) : ℝ) * (c) * ((((-1) * (c ^ 2)) + (b * c)))^2 + ((5 / 6) : ℝ) * (b) * ((((-1) * (b ^ 2)) + (a * c)))^2 + ((1 / 9) : ℝ) * (b) * (((b ^ 2) + ((-1) * b * c)))^2 + ((1 / 18) : ℝ) * (b) * (((b ^ 2) + ((-1) * (c ^ 2))))^2 + ((1 / 9) : ℝ) * (a) * (((a ^ 2) + ((-1) * a * c)))^2 + ((5 / 6) : ℝ) * (a) * (((a ^ 2) + ((-1) * b * c)))^2 + ((1 / 18) : ℝ) * (a) * (((a ^ 2) + ((-1) * (c ^ 2))))^2 := by positivity
      _ = (a^5 + b^5 + c^5) - (a * b * c * (a^2 + b^2 + c^2 + (2 / 3) * (a - b)^2)) := by ring
  exact sub_nonneg.mp h
