-- Prove2me | solution 1 for lean_workbook_plus_41163
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:32:54.544798+00:00
-- url     : https://prove2.me/submissions/75438105-3194-49b3-8062-b3e2da1df8b7

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ t : ℝ, t ≤ 1 → 1 / (1 + t ^ 2) ≤ 27 * (2 - t) / 50 := by
  intro t ht
  apply (div_le_iff₀ (show 0 < 1+t^2 by positivity)).2
  have hp := mul_nonneg (sq_nonneg (3*t-1)) (show 0 ≤ 4-3*t by linarith)
  nlinarith only [hp]
