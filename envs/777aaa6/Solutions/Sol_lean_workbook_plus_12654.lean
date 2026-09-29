-- Prove2me | solution 1 for lean_workbook_plus_12654
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:32:22.352755+00:00
-- url     : https://prove2.me/submissions/80167820-6990-44d9-b1dd-51aa7d03ce87

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x : ℝ) : x ^ 4 - x ^ 3 - x + 1 ≥ 0 := by
  intros
  
  have h_identity : (x ^ 4 - x ^ 3 - x + 1) - (0) = (1 : ℝ) * 1 * ((1 + ((-1 / 2) * x) + ((-1 / 2) * (x ^ 2))))^2 + ((3 / 4) : ℝ) * 1 * ((x + ((-1) * (x ^ 2))))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (x ^ 4 - x ^ 3 - x + 1) - (0) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
