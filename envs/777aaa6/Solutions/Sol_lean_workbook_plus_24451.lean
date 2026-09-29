-- Prove2me | solution 1 for lean_workbook_plus_24451
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:57:35.885808+00:00
-- url     : https://prove2.me/submissions/63d7970f-e226-4334-a8c5-f54c9101c81d

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a : ℝ)
  (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = a * x)
  (h₁ : 2008 * a = 3012) :
  f 2009 = 3012 * 2009 / 2008 := by
  rw [h₀]
  linarith
