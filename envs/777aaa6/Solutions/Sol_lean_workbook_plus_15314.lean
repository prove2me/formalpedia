-- Prove2me | solution 1 for lean_workbook_plus_15314
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:15:02.95372+00:00
-- url     : https://prove2.me/submissions/991aee67-2808-4892-8e99-2f657650b091

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b : ℝ) : a ^ 6 + 3 * a ^ 4 * b ^ 2 + 8 * b ^ 6 ≥ 2 * a ^ 3 * b ^ 3 + 2 * a ^ 2 * b ^ 4 + 8 * a * b ^ 5 := by
  intros
  
  have h_identity : (a ^ 6 + 3 * a ^ 4 * b ^ 2 + 8 * b ^ 6) - (2 * a ^ 3 * b ^ 3 + 2 * a ^ 2 * b ^ 4 + 8 * a * b ^ 5) = (1 : ℝ) * 1 * ((((-2) * (b ^ 3)) + (a * (b ^ 2)) + (b * (a ^ 2))))^2 + (1 : ℝ) * 1 * (((a ^ 3) + ((-2) * (b ^ 3)) + (a * (b ^ 2))))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (a ^ 6 + 3 * a ^ 4 * b ^ 2 + 8 * b ^ 6) - (2 * a ^ 3 * b ^ 3 + 2 * a ^ 2 * b ^ 4 + 8 * a * b ^ 5) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
