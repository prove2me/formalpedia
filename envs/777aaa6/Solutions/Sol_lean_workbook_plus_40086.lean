-- Prove2me | solution 1 for lean_workbook_plus_40086
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T02:09:21.469918+00:00
-- url     : https://prove2.me/submissions/c2c2dfc5-ab18-48b0-9623-b5d40827180b

import Mathlib.Analysis.Complex.Basic

theorem solution (f : ℤ → ℤ) (hf: f = fun x ↦ x) : ∀ x y, f (f x + x * f y) = x * y + f x := by
  intro x y
  subst hf
  simp only
  ring
