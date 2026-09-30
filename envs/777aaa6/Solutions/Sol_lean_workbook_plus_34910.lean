-- Prove2me | solution 1 for lean_workbook_plus_34910
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T03:24:08.883421+00:00
-- url     : https://prove2.me/submissions/455e17c3-6a9d-41eb-a010-9944aceaabdd

import Mathlib.Analysis.Complex.Basic

theorem solution (f : ℝ → ℝ) (hf : ∀ t, f t = 0 ∨ ∀ t, f t = t ^ 2) : (∀ α ≠ 0, f α = 0 → ∀ x, f x = 0) ∨ (∀ x ≠ 0, f x ≠ 0 → ∀ x, f x = x ^ 2) := by
  right
  intro x _ hfx
  rcases hf x with h | h
  · exact absurd h hfx
  · exact h
