-- Prove2me | solution 1 for lean_workbook_plus_10240
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:30:16.583336+00:00
-- url     : https://prove2.me/submissions/d86a096f-fe9c-41af-9412-ccf11e35c023

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x y z : ℝ) : x ^ 4 + y ^ 4 + z ^ 4 + x * y * z * (x + y + z) ≥ x ^ 3 * y + y ^ 3 * z + z ^ 3 * x + x * y ^ 3 + y * z ^ 3 + z * x ^ 3 := by
  intros
  
  have h_identity : (x ^ 4 + y ^ 4 + z ^ 4 + x * y * z * (x + y + z)) - (x ^ 3 * y + y ^ 3 * z + z ^ 3 * x + x * y ^ 3 + y * z ^ 3 + z * x ^ 3) = (1 : ℝ) * 1 * (((x ^ 2) + ((-1 / 2) * (y ^ 2)) + ((-1 / 2) * (z ^ 2)) + (y * z) + ((-1 / 2) * x * y) + ((-1 / 2) * x * z)))^2 + ((3 / 4) : ℝ) * 1 * (((z ^ 2) + ((-1) * (y ^ 2)) + (x * y) + ((-1) * x * z)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (x ^ 4 + y ^ 4 + z ^ 4 + x * y * z * (x + y + z)) - (x ^ 3 * y + y ^ 3 * z + z ^ 3 * x + x * y ^ 3 + y * z ^ 3 + z * x ^ 3) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
