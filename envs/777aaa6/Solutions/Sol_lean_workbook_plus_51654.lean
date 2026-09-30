-- Prove2me | solution 1 for lean_workbook_plus_51654
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:14:24.622856+00:00
-- url     : https://prove2.me/submissions/f68aa96f-cf14-4296-bb8d-1f59095432d2

import Mathlib.Analysis.Complex.Basic

theorem solution (f : ℤ → ℤ) (hf: f = fun x ↦ x) : ∀ x y, f (f x + y) = 2 * x + f (f y - x) := by
  subst hf
  intro x y
  simp only
  ring
