-- Prove2me | solution 1 for lean_workbook_plus_75821
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T23:06:13.946897+00:00
-- url     : https://prove2.me/submissions/bf2796be-be41-426a-9e1a-2eda56312e36

import Mathlib.Analysis.Complex.Basic

theorem solution (f : ℤ → ℤ) (hf: f = fun x ↦ x) : ∀ x y, f (x * f y - 1) + f (x * y) = 2 * x * y - 1 := by
  intro x y
  subst hf
  simp only
  ring
