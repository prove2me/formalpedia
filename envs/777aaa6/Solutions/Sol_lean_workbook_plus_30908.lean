-- Prove2me | solution 1 for lean_workbook_plus_30908
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:28:37.385607+00:00
-- url     : https://prove2.me/submissions/6b6e2421-1f98-48f5-a0a5-1343fd3fa59b

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution : ∀ z : ℝ, 1 ≤ z → 2 * z / (1 / z + z) ≥ 1 := by
  intro z hz
  have hp : 0 < z := by linarith
  have hden : 0 < 1 / z + z := by positivity
  have hi : 1 / z ≤ 1 := (div_le_one hp).2 hz
  exact (le_div_iff₀ hden).2 (by nlinarith)
