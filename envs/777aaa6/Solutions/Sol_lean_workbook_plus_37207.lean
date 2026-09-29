-- Prove2me | solution 1 for lean_workbook_plus_37207
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:11:01.413707+00:00
-- url     : https://prove2.me/submissions/40c4b65a-00dc-4347-b777-eb7d8dfa9bd7

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000


theorem solution (x : ℝ) (hx : abs x ≤ 1) : abs (x^2 - x - 2) ≤ 3 * abs (x + 1) := by
  obtain ⟨hl, hu⟩ := abs_le.mp hx
  have hq : x^2 - x - 2 ≤ 0 := by nlinarith [sq_nonneg x]
  rw [abs_of_nonpos hq, abs_of_nonneg (by linarith : 0 ≤ x + 1)]
  nlinarith
