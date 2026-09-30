-- Prove2me | solution 1 for lean_workbook_plus_32950
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:12:47.830956+00:00
-- url     : https://prove2.me/submissions/415abbb7-cd40-45cb-b363-5564a3fa08e3

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (x : ℝ) (hx : ∀ ε > 0, 0 ≤ x ∧ x < ε) : x = 0 := by
  by_contra hne
  have hpos : 0 < x := lt_of_le_of_ne (hx 1 (by norm_num)).1 (Ne.symm hne)
  exact (lt_irrefl x) (hx x hpos).2

#print axioms solution
