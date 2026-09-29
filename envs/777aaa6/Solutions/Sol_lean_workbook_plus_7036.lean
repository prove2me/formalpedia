-- Prove2me | solution 1 for lean_workbook_plus_7036
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:14:06.53565+00:00
-- url     : https://prove2.me/submissions/83c49368-e8f8-4280-8d08-1e035cee6b37

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x y z : ℝ) : 4 * z ^ 2 + (x + y) ^ 2 ≥ 4 * z * (x + y) := by
  intros
  
  have h_identity : (4 * z ^ 2 + (x + y) ^ 2) - (4 * z * (x + y)) = (1 : ℝ) * 1 * ((x + y + ((-2) * z)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (4 * z ^ 2 + (x + y) ^ 2) - (4 * z * (x + y)) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
