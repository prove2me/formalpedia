-- Prove2me | solution 1 for lean_workbook_plus_36800
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:28:08.916454+00:00
-- url     : https://prove2.me/submissions/043ad581-6105-4ef8-9ba3-1a199519cee1

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (f : ℝ → ℝ)
  (h₀ : ∀ x y, f (x + y) = f x + 2 * f y)
  (h₁ : ∀ x, f (x + 1) = 2 * f x)
  : ∀ x, f x = 0 := by
  intro x
  have h0 := h₀ 0 0
  have hx := h₀ 0 x
  simp only [zero_add] at h0 hx
  linarith
