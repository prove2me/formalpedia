-- Prove2me | solution 1 for lean_workbook_plus_28633
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:14:24.509358+00:00
-- url     : https://prove2.me/submissions/b51f8ddb-5925-4b44-bcef-4650b4af68b4

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution : ∀ a b c : ℝ, a * b * (a ^ 2 + b ^ 2) + b * c * (b ^ 2 + c ^ 2) + c * a * (c ^ 2 + a ^ 2) ≤ 2 * a ^ 4 + 2 * b ^ 4 + 2 * c ^ 4 := by
  intro a b c
  intros
  
  have h_identity : (2 * a ^ 4 + 2 * b ^ 4 + 2 * c ^ 4) - (a * b * (a ^ 2 + b ^ 2) + b * c * (b ^ 2 + c ^ 2) + c * a * (c ^ 2 + a ^ 2)) = (2 : ℝ) * 1 * (((a ^ 2) + ((-1 / 8) * (b ^ 2)) + ((-1 / 8) * (c ^ 2)) + ((-1 / 4) * a * b) + ((-1 / 4) * a * c) + ((-1 / 4) * b * c)))^2 + ((3 / 8) : ℝ) * 1 * ((((-3 / 2) * (b ^ 2)) + ((-3 / 2) * (c ^ 2)) + (a * b) + (a * c) + (b * c)))^2 + ((9 / 8) : ℝ) * 1 * (((b ^ 2) + ((-1) * (c ^ 2))))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (2 * a ^ 4 + 2 * b ^ 4 + 2 * c ^ 4) - (a * b * (a ^ 2 + b ^ 2) + b * c * (b ^ 2 + c ^ 2) + c * a * (c ^ 2 + a ^ 2)) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
