-- Prove2me | solution 1 for lean_workbook_plus_29720
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T20:58:09.738767+00:00
-- url     : https://prove2.me/submissions/417f5b85-e8f6-437a-9de7-51c3836b247c

import Mathlib
set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (a b c : ℝ) (hf: ∀ x > 0, f (x + c) = a * x + b) : ∃ d, ∀ x > c, f x = a * x + d   := by
  use b - a*c
  intro x hx
  have h := hf (x - c) (sub_pos.mpr hx)
  simp at h
  linarith

#print axioms solution
