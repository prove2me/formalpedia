-- Prove2me | solution 1 for lean_workbook_plus_46182
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:54:08.423532+00:00
-- url     : https://prove2.me/submissions/0e0b8057-697f-45c5-ab45-36e4ab9c86bf

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution : ∀ t : ℝ, 2 * (t ^ 2 - t + 1) / (t ^ 2 + 1) ≥ 1 := by
  intro t
  apply (le_div_iff₀ (show 0 < t^2+1 by positivity)).2
  nlinarith [sq_nonneg (t-1)]
