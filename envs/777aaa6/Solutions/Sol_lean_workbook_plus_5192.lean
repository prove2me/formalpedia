-- Prove2me | solution 1 for lean_workbook_plus_5192
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:13:19.780754+00:00
-- url     : https://prove2.me/submissions/370508c4-1689-4c18-94ff-4f5ee2e59fc1

import Mathlib.Analysis.Complex.Basic

theorem solution (f : ℤ → ℤ) (hf: f = fun x ↦ x) : ∀ x y, f (x^2 + x*y + y) = f x^2 + f (x + 1) * f y := by
  intro x y
  subst hf
  ring
