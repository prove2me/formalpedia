-- Prove2me | solution 1 for lean_workbook_plus_11789
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:50:51.936678+00:00
-- url     : https://prove2.me/submissions/75574d7b-23e4-45ca-bf0d-01cf517d6ad8

import Mathlib
set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (hf : ∀ x y, f (x + y) = f x * f y) (h : f 0 ≠ 0) : ∀ x, f x ≠ 0   := by
  intro x hx
  apply h
  simpa [hx] using hf x (-x)

#print axioms solution
