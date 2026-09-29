-- Prove2me | solution 1 for lean_workbook_plus_47413
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:18:55.462158+00:00
-- url     : https://prove2.me/submissions/01e5041a-e4fa-4d32-b48e-2d5f44d978c0

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b : ℝ) :
  (1 + a^4) * (1 + b^4) ≥ (1 + a^2 * b^2) * (a^2 + b^2) := by
  intros
  have h : (0 : ℝ) ≤ ((1 + a^4) * (1 + b^4)) - ((1 + a^2 * b^2) * (a^2 + b^2)) := by
    calc
      0 ≤ ((1 / 2) : ℝ) * ((1 + ((-1) * (b ^ 2))))^2 + ((1 / 2) : ℝ) * ((1 + ((-1) * (a ^ 2))))^2 + ((1 / 2) : ℝ) * (((b ^ 2) + ((-1) * (a ^ 2) * (b ^ 2))))^2 + ((1 / 2) : ℝ) * (((a ^ 2) + ((-1) * (a ^ 2) * (b ^ 2))))^2 := by positivity
      _ = ((1 + a^4) * (1 + b^4)) - ((1 + a^2 * b^2) * (a^2 + b^2)) := by ring
  exact sub_nonneg.mp h
