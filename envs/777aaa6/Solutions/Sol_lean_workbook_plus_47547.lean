-- Prove2me | solution 1 for lean_workbook_plus_47547
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:14:14.42654+00:00
-- url     : https://prove2.me/submissions/c323d818-6e28-4b0d-8451-d6f10dd1be74

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) : 2 * (a ^ 4 + b ^ 4 + c ^ 4 + a ^ 2 * b * c + b ^ 2 * a * c + c ^ 2 * a * b) ≥ 2 * (a ^ 3 * b + a ^ 3 * c + b ^ 3 * a + b ^ 3 * c + c ^ 3 * a + c ^ 3 * b) := by
  intros
  
  have h_identity : (2 * (a ^ 4 + b ^ 4 + c ^ 4 + a ^ 2 * b * c + b ^ 2 * a * c + c ^ 2 * a * b)) - (2 * (a ^ 3 * b + a ^ 3 * c + b ^ 3 * a + b ^ 3 * c + c ^ 3 * a + c ^ 3 * b)) = (2 : ℝ) * 1 * (((a ^ 2) + ((-1 / 2) * (b ^ 2)) + ((-1 / 2) * (c ^ 2)) + (b * c) + ((-1 / 2) * a * b) + ((-1 / 2) * a * c)))^2 + ((3 / 2) : ℝ) * 1 * (((c ^ 2) + ((-1) * (b ^ 2)) + (a * b) + ((-1) * a * c)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (2 * (a ^ 4 + b ^ 4 + c ^ 4 + a ^ 2 * b * c + b ^ 2 * a * c + c ^ 2 * a * b)) - (2 * (a ^ 3 * b + a ^ 3 * c + b ^ 3 * a + b ^ 3 * c + c ^ 3 * a + c ^ 3 * b)) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
