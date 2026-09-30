-- Prove2me | solution 1 for lean_workbook_plus_32403
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:42:01.547715+00:00
-- url     : https://prove2.me/submissions/10174566-6fbd-4a82-b68f-edd313b86cec

import Mathlib.Analysis.Complex.Basic

theorem solution (f : ℤ → ℤ) (hf: f = fun x ↦ x) : ∀ x y, f (f x + y) + f (f y + x) = f (2 * x + f (2 * y)) := by
  intro x y
  subst hf
  beta_reduce
  ring
