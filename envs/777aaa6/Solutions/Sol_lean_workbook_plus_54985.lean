-- Prove2me | solution 1 for lean_workbook_plus_54985
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:14:07.925307+00:00
-- url     : https://prove2.me/submissions/1d32a3b7-b1c4-49cf-94e9-32212335b21b

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : a^2 + b^2 + 1 ≥ a + b + a * b := by
  intros
  
  have h_identity : (a^2 + b^2 + 1) - (a + b + a * b) = ((1 / 2) : ℝ) * 1 * ((1 + ((-1) * a)))^2 + ((1 / 2) : ℝ) * 1 * ((1 + ((-1) * b)))^2 + ((1 / 2) : ℝ) * 1 * ((a + ((-1) * b)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (a^2 + b^2 + 1) - (a + b + a * b) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
