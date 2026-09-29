-- Prove2me | solution 1 for lean_workbook_plus_57996
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:32:33.977524+00:00
-- url     : https://prove2.me/submissions/ca4af0b9-2e36-4b86-b94c-234e1e67fc5c

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x y z : ℝ) : 9 * x ^ 2 + 25 * y ^ 2 + 225 * z ^ 2 ≥ 15 * (x * y + 3 * x * z + 5 * y * z) := by
  intros
  
  have h_identity : (9 * x ^ 2 + 25 * y ^ 2 + 225 * z ^ 2) - (15 * (x * y + 3 * x * z + 5 * y * z)) = (9 : ℝ) * 1 * ((x + ((-5 / 2) * z) + ((-5 / 6) * y)))^2 + ((75 / 4) : ℝ) * 1 * ((y + ((-3) * z)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (9 * x ^ 2 + 25 * y ^ 2 + 225 * z ^ 2) - (15 * (x * y + 3 * x * z + 5 * y * z)) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
