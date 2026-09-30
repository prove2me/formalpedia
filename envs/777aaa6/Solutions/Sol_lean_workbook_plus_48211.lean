-- Prove2me | solution 1 for lean_workbook_plus_48211
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T02:10:50.731459+00:00
-- url     : https://prove2.me/submissions/8c0cfd12-c95a-4821-8062-8ceff764c197

import Mathlib.Analysis.Complex.Basic

theorem solution (f : ℤ → ℤ) (hf: f = fun x ↦ x) : ∀ x y, f ((x - y) * f x) = f (y * f (x - y)) + (x - y) ^ 2 := by
  subst hf
  intro x y
  simp only
  ring
