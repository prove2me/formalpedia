-- Prove2me | solution 1 for lean_workbook_plus_1383
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:30:43.107513+00:00
-- url     : https://prove2.me/submissions/1593c7ce-d639-4d82-84f8-a6ea2004d27f

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x y z : ℝ) : (x ^ 2 / 4 + y ^ 2 + z ^ 2) ≥ x * y - x * z + 2 * y * z := by
  intros
  
  have h_identity : ((x ^ 2 / 4 + y ^ 2 + z ^ 2)) - (x * y - x * z + 2 * y * z) = ((1 / 4) : ℝ) * 1 * ((x + ((-2) * y) + (2 * z)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((x ^ 2 / 4 + y ^ 2 + z ^ 2)) - (x * y - x * z + 2 * y * z) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
