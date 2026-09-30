-- Prove2me | solution 1 for lean_workbook_plus_17255
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:16:56.73806+00:00
-- url     : https://prove2.me/submissions/2689b5f4-3bab-4f86-9ed9-3497c57aedd0

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (ζ : ℂ) (h : ζ ^ 3 = 1) (h' : ζ ≠ 1) : 1 + ζ + ζ ^ 2 = 0 := by
  have h1 : (ζ - 1) * (1 + ζ + ζ ^ 2) = ζ ^ 3 - 1 := by ring
  rw [h, sub_self] at h1
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact absurd (sub_eq_zero.mp h2) h'
  · exact h2

#print axioms solution
