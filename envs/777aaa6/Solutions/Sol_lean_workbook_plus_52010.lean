-- Prove2me | solution 1 for lean_workbook_plus_52010
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:30:30.118202+00:00
-- url     : https://prove2.me/submissions/498e2905-455c-408e-8b31-e32b95a99399

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x y : ℝ) :
  (x * y + x + y - 1) ^ 2 ≤ 2 * (x ^ 2 + 1) * (y ^ 2 + 1) := by
  intros
  
  have h_identity : (2 * (x ^ 2 + 1) * (y ^ 2 + 1)) - ((x * y + x + y - 1) ^ 2) = (1 : ℝ) * 1 * ((1 + x + y + ((-1) * x * y)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (2 * (x ^ 2 + 1) * (y ^ 2 + 1)) - ((x * y + x + y - 1) ^ 2) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
