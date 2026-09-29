-- Prove2me | solution 1 for lean_workbook_plus_35569
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:14:20.040352+00:00
-- url     : https://prove2.me/submissions/ebbbeaf0-8059-43fe-a928-6a7c8d7199e1

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x z : ℝ) : x ^ 4 + z ^ 4 + 2 * x * z ^ 3 ≥ 2 * x ^ 3 * z + x ^ 2 * z ^ 2 := by
  intros
  
  have h_identity : (x ^ 4 + z ^ 4 + 2 * x * z ^ 3) - (2 * x ^ 3 * z + x ^ 2 * z ^ 2) = (1 : ℝ) * 1 * (((x ^ 2) + ((-1) * (z ^ 2)) + ((-1) * x * z)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (x ^ 4 + z ^ 4 + 2 * x * z ^ 3) - (2 * x ^ 3 * z + x ^ 2 * z ^ 2) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
