-- Prove2me | solution 1 for lean_workbook_plus_3470
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:00:44.872198+00:00
-- url     : https://prove2.me/submissions/385f679a-4d7a-4b0e-b57d-7406390b87a6

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x y : ℝ)
  (f : ℝ → ℝ)
  (h₀ : ∀ z, f z = 3 * (z - 3)^2 + 7 * (z - 3) + 4)
  (h₁ : y = f x) :
  y = 3 * x^2 - 11 * x + 10 := by
  rw [h₁, h₀]
  ring
