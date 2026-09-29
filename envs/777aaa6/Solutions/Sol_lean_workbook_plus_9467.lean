-- Prove2me | solution 1 for lean_workbook_plus_9467
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:00:34.7598+00:00
-- url     : https://prove2.me/submissions/66d26c4b-11af-41ef-8c63-bf84ecb47cdc

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = x^5 + 6 * x^4 + 7 * x^3 - 20 * x^2 - 42 * x - 20)
  (h₁ : f 2 = 0) :
  ∀ x, f x = (x - 2) * (x + 1)^2 * (x^2 + 6 * x + 10) := by
  intro x
  rw [h₀]
  ring
