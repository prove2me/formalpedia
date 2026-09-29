-- Prove2me | solution 1 for lean_workbook_plus_64337
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:36:31.382808+00:00
-- url     : https://prove2.me/submissions/b90f02e7-52ce-4c47-8806-e9599228ce2b

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^5 * c^2 + b^5 * a^2 + c^5 * b^2 ≥ a * b * c * (a^3 * c + b^3 * a + c^3 * b) := by
  intros
  have hpos_a : (0 : ℝ) ≤ a := by first | positivity | linarith
  have hpos_b : (0 : ℝ) ≤ b := by first | positivity | linarith
  have hpos_c : (0 : ℝ) ≤ c := by first | positivity | linarith
  have h : (0 : ℝ) ≤ (a^5 * c^2 + b^5 * a^2 + c^5 * b^2) - (a * b * c * (a^3 * c + b^3 * a + c^3 * b)) := by
    calc
      0 ≤ ((1 / 3) : ℝ) * (c) * (((a * (b ^ 2)) + ((-1) * b * (c ^ 2))))^2 + ((2 / 3) : ℝ) * (c) * ((((-1) * b * (c ^ 2)) + (a * b * c)))^2 + ((1 / 3) : ℝ) * (b) * (((c * (a ^ 2)) + ((-1) * a * (b ^ 2))))^2 + ((2 / 3) : ℝ) * (b) * (((a * (b ^ 2)) + ((-1) * a * b * c)))^2 + ((2 / 3) : ℝ) * (a) * (((c * (a ^ 2)) + ((-1) * a * b * c)))^2 + ((1 / 3) : ℝ) * (a) * (((c * (a ^ 2)) + ((-1) * b * (c ^ 2))))^2 + ((1 / 3) : ℝ) * ((a * b * c)) * (((a * b) + ((-1) * a * c)))^2 + ((1 / 3) : ℝ) * ((a * b * c)) * (((a * b) + ((-1) * b * c)))^2 + ((1 / 3) : ℝ) * ((a * b * c)) * (((a * c) + ((-1) * b * c)))^2 := by positivity
      _ = (a^5 * c^2 + b^5 * a^2 + c^5 * b^2) - (a * b * c * (a^3 * c + b^3 * a + c^3 * b)) := by ring
  exact sub_nonneg.mp h
