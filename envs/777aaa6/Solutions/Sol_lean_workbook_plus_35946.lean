-- Prove2me | solution 1 for lean_workbook_plus_35946
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:25:45.123839+00:00
-- url     : https://prove2.me/submissions/eb6bb38c-f824-413e-9d4a-69662eb1babd

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) : (a^2 + b^2 + c^2)^3 ≥ 3 * (a^2 * b + b^2 * c + c^2 * a)^2 := by
  intros
  have h : (0 : ℝ) ≤ ((a^2 + b^2 + c^2)^3) - (3 * (a^2 * b + b^2 * c + c^2 * a)^2) := by
    calc
      0 ≤ (1 : ℝ) * (((c ^ 3) + ((-1) * a * (b ^ 2))))^2 + (2 : ℝ) * (((b * (c ^ 2)) + ((-1) * a * b * c)))^2 + (1 : ℝ) * ((((-1) * (a ^ 3)) + (b * (c ^ 2))))^2 + (1 : ℝ) * (((b ^ 3) + ((-1) * c * (a ^ 2))))^2 + (2 : ℝ) * ((((-1) * a * (b ^ 2)) + (a * b * c)))^2 + (2 : ℝ) * ((((-1) * c * (a ^ 2)) + (a * b * c)))^2 := by positivity
      _ = ((a^2 + b^2 + c^2)^3) - (3 * (a^2 * b + b^2 * c + c^2 * a)^2) := by ring
  exact sub_nonneg.mp h
