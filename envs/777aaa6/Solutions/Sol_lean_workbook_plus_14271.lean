-- Prove2me | solution 1 for lean_workbook_plus_14271
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T03:23:10.933182+00:00
-- url     : https://prove2.me/submissions/bd613ba5-fd69-4465-b2b7-d6fd50720dd2

import Mathlib.Analysis.Complex.Basic

theorem solution (f : ℝ → ℝ) (hf: f = id ∨ f = abs) : ∀ x, f x = x ∨ ∀ x, f x = |x| := by
  intro x
  rcases hf with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr fun y => rfl
