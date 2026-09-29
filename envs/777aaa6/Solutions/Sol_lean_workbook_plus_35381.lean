-- Prove2me | solution 1 for lean_workbook_plus_35381
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:15:11.957557+00:00
-- url     : https://prove2.me/submissions/13151876-c070-4c52-96a8-439e37e0fe4f

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) : a^2 + b^2 + c^2 - a * b - b * c - c * a ≥ 3 * (a - b) * (b - c) := by
  intros
  
  have h_identity : (a^2 + b^2 + c^2 - a * b - b * c - c * a) - (3 * (a - b) * (b - c)) = (1 : ℝ) * 1 * ((a + c + ((-2) * b)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (a^2 + b^2 + c^2 - a * b - b * c - c * a) - (3 * (a - b) * (b - c)) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
