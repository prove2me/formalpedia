-- Prove2me | solution 1 for lean_workbook_plus_55989
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:18:47.182469+00:00
-- url     : https://prove2.me/submissions/0620a345-13c2-424c-ac91-654798c2f965

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) : a ^ 4 * b ^ 2 + b ^ 4 * c ^ 2 + c ^ 4 * a ^ 2 ≥ a * b ^ 2 * c ^ 3 + b * c ^ 2 * a ^ 3 + c * a ^ 2 * b ^ 3 := by
  intros
  have h : (0 : ℝ) ≤ (a ^ 4 * b ^ 2 + b ^ 4 * c ^ 2 + c ^ 4 * a ^ 2) - (a * b ^ 2 * c ^ 3 + b * c ^ 2 * a ^ 3 + c * a ^ 2 * b ^ 3) := by
    calc
      0 ≤ ((1 / 2) : ℝ) * (((c * (b ^ 2)) + ((-1) * a * (c ^ 2))))^2 + ((1 / 2) : ℝ) * (((c * (b ^ 2)) + ((-1) * b * (a ^ 2))))^2 + ((1 / 2) : ℝ) * (((a * (c ^ 2)) + ((-1) * b * (a ^ 2))))^2 := by positivity
      _ = (a ^ 4 * b ^ 2 + b ^ 4 * c ^ 2 + c ^ 4 * a ^ 2) - (a * b ^ 2 * c ^ 3 + b * c ^ 2 * a ^ 3 + c * a ^ 2 * b ^ 3) := by ring
  exact sub_nonneg.mp h
