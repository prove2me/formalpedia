-- Prove2me | solution 1 for lean_workbook_plus_15603
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:06:20.305319+00:00
-- url     : https://prove2.me/submissions/1645774c-d656-4292-9ba9-98fc4b0a96fc

import Mathlib.Analysis.Complex.Basic

theorem solution (f : ℝ → ℝ) (hf: f '' Set.univ = Set.univ) (h: ∀ x, f x - x ^ 2 = 0) : ∀ x, f x = x ^ 2 := by
  intro x
  have := h x
  linarith
