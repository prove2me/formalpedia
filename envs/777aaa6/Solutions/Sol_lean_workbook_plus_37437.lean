-- Prove2me | solution 1 for lean_workbook_plus_37437
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:24:34.320949+00:00
-- url     : https://prove2.me/submissions/d6a59069-3a2d-4cf8-be52-0327c82934e7

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000


theorem solution : ¬ ∃ x : ℝ, x^4 + x^3 + x^2 + x + 1 = 0 := by
  rintro ⟨x, hx⟩
  nlinarith [sq_nonneg (x^2 + x/2), sq_nonneg (x/2 + 1)]
