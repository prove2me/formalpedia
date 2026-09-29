-- Prove2me | solution 1 for lean_workbook_plus_67026
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:06:25.598679+00:00
-- url     : https://prove2.me/submissions/d100d969-ca3a-4f5d-be60-d765f1c86400

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) :
  a^2 * (b - c)^4 + b^2 * (c - a)^4 + c^2 * (a - b)^4 ≥
  1 / 2 * (a - b)^2 * (b - c)^2 * (c - a)^2 := by
  intros
  
  have h_identity : (a^2 * (b - c)^4 + b^2 * (c - a)^4 + c^2 * (a - b)^4) - (1 / 2 * (a - b)^2 * (b - c)^2 * (c - a)^2) = ((1 / 2) : ℝ) * 1 * (((a * (b ^ 2)) + (a * (c ^ 2)) + (b * (a ^ 2)) + (b * (c ^ 2)) + (c * (a ^ 2)) + (c * (b ^ 2)) + ((-6) * a * b * c)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (a^2 * (b - c)^4 + b^2 * (c - a)^4 + c^2 * (a - b)^4) - (1 / 2 * (a - b)^2 * (b - c)^2 * (c - a)^2) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
