-- Prove2me | solution 1 for lean_workbook_plus_15362
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T01:19:52.562455+00:00
-- url     : https://prove2.me/submissions/61ad6a8c-2fe4-4635-a7ce-cc0cd10e1f67

import Mathlib.Analysis.Complex.Basic

theorem solution (f : ℤ → ℤ) (hf: f = fun x ↦ x) : ∀ x y, f (f (x + y) - x) * f (f (x + y) - y) = x * y := by
  intro x y
  subst hf
  simp only
  ring
