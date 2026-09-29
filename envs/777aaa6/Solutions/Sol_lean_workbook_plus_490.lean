-- Prove2me | solution 1 for lean_workbook_plus_490
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:18:52.842105+00:00
-- url     : https://prove2.me/submissions/12b15cc9-b307-4c38-b737-70d937cc9c68

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) : 27 * (a ^ 2 + b ^ 2 + c ^ 2) * (a * b + b * c + c * a) ^ 2 ≥ 81 * a * b * c * (a + b + c) * (a ^ 2 + b ^ 2 + c ^ 2) := by
  intros
  have h : (0 : ℝ) ≤ (27 * (a ^ 2 + b ^ 2 + c ^ 2) * (a * b + b * c + c * a) ^ 2) - (81 * a * b * c * (a + b + c) * (a ^ 2 + b ^ 2 + c ^ 2)) := by
    calc
      0 ≤ ((27 / 2) : ℝ) * (((b * (c ^ 2)) + ((-1) * a * (c ^ 2))))^2 + ((27 / 2) : ℝ) * (((b * (c ^ 2)) + ((-1) * a * b * c)))^2 + ((27 / 2) : ℝ) * (((c * (b ^ 2)) + ((-1) * a * b * c)))^2 + ((27 / 2) : ℝ) * (((c * (b ^ 2)) + ((-1) * a * (b ^ 2))))^2 + ((27 / 2) : ℝ) * (((a * (c ^ 2)) + ((-1) * a * b * c)))^2 + ((27 / 2) : ℝ) * ((((-1) * a * (b ^ 2)) + (a * b * c)))^2 + ((27 / 2) : ℝ) * ((((-1) * c * (a ^ 2)) + (a * b * c)))^2 + ((27 / 2) : ℝ) * ((((-1) * b * (a ^ 2)) + (a * b * c)))^2 + ((27 / 2) : ℝ) * (((c * (a ^ 2)) + ((-1) * b * (a ^ 2))))^2 := by positivity
      _ = (27 * (a ^ 2 + b ^ 2 + c ^ 2) * (a * b + b * c + c * a) ^ 2) - (81 * a * b * c * (a + b + c) * (a ^ 2 + b ^ 2 + c ^ 2)) := by ring
  exact sub_nonneg.mp h
