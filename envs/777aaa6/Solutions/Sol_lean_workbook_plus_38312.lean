-- Prove2me | solution 1 for lean_workbook_plus_38312
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:54:55.693522+00:00
-- url     : https://prove2.me/submissions/8cc8b553-c8ac-488c-a385-1378952c321a

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (a b t p : ℝ) (h₁ : t = a + b) (h₂ : p = a * b) (h₃ : 2 * t ^ 2 - 2 * p = 1) : t ^ 2 ≤ 2 / 3 := by
  rw [h₁,h₂] at h₃
  rw [h₁]
  nlinarith [sq_nonneg (a-b)]
