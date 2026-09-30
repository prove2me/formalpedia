-- Prove2me | solution 1 for lean_workbook_plus_54229
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:14:38.947112+00:00
-- url     : https://prove2.me/submissions/d03a3fc9-6c58-4289-9d27-a664a11749b7

import Mathlib.Analysis.Complex.Basic

theorem solution (p : ℕ) (hp : p.Prime) (n : ℕ) (h : p > 2) : ∃ x y : ℕ, (2*x+1)^2 = (p^n * (2*y+1))^2 - p^(2*n) + 1 := by
  refine ⟨0, 0, ?_⟩
  have h1 : (p^n * (2*0+1))^2 = p^(2*n) := by ring
  rw [h1]
  simp
