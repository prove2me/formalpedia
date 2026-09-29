-- Prove2me | solution 1 for lean_workbook_plus_9448
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:31:08.105833+00:00
-- url     : https://prove2.me/submissions/b65e4f34-c1f6-4eba-baf4-3eb7691da2a7

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x y z : ℝ) : 21 + 4 * (x * y + y * z + z * x) + 3 * (x ^ 2 + y ^ 2 + z ^ 2) ≥ 14 * (x + y + z) := by
  intros
  
  have h_identity : (21 + 4 * (x * y + y * z + z * x) + 3 * (x ^ 2 + y ^ 2 + z ^ 2)) - (14 * (x + y + z)) = (21 : ℝ) * 1 * ((1 + ((-1 / 3) * x) + ((-1 / 3) * y) + ((-1 / 3) * z)))^2 + ((2 / 3) : ℝ) * 1 * ((x + ((-1 / 2) * y) + ((-1 / 2) * z)))^2 + ((1 / 2) : ℝ) * 1 * ((y + ((-1) * z)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (21 + 4 * (x * y + y * z + z * x) + 3 * (x ^ 2 + y ^ 2 + z ^ 2)) - (14 * (x + y + z)) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
