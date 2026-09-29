-- Prove2me | solution 1 for lean_workbook_plus_31610
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:14:25.650272+00:00
-- url     : https://prove2.me/submissions/5bd2b04a-20f9-4968-8ac2-98ec9f295b0b

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + 1) ^ 2 * (b + 1) ^ 2 * (c + 1) ^ 2 ≥ 4 * (a + b + c + 1) * (a * b + b * c + c * a + a * b * c) := by
  intros
  
  have h_identity : ((a + 1) ^ 2 * (b + 1) ^ 2 * (c + 1) ^ 2) - (4 * (a + b + c + 1) * (a * b + b * c + c * a + a * b * c)) = (1 : ℝ) * 1 * ((1 + a + b + c + ((-1) * a * b) + ((-1) * a * c) + ((-1) * b * c) + ((-1) * a * b * c)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((a + 1) ^ 2 * (b + 1) ^ 2 * (c + 1) ^ 2) - (4 * (a + b + c + 1) * (a * b + b * c + c * a + a * b * c)) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
