-- Prove2me | solution 1 for lean_workbook_plus_63067
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:10:32.926929+00:00
-- url     : https://prove2.me/submissions/7cb382a5-dd95-4030-bff5-a1ea8856c1d1

import Mathlib
set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (x : ℝ) (h : ∀ x, f x = f (-x)) : ∀ x, f (x - 1) = f (1 - x)   := by
  intro x
  simpa only [neg_sub] using h (x - 1)

#print axioms solution
