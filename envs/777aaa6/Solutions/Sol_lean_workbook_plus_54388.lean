-- Prove2me | solution 1 for lean_workbook_plus_54388
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:29:56.605522+00:00
-- url     : https://prove2.me/submissions/915b6708-088e-453c-a215-ba37393f0351

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (f g : ℝ → ℝ)
  (hf : ∀ x, 0 < f x)
  (hg : ∀ x, 0 < g x)
  (hf' : ∀ x y, x ≤ y → f x ≤ f y)
  (hg' : ∀ x y, x ≤ y → g x ≤ g y)
  : ∀ x y, x ≤ y → f x * g x ≤ f y * g y := by
  intro x y h
  exact mul_le_mul (hf' x y h) (hg' x y h) (le_of_lt (hg x)) (le_of_lt (hf y))
