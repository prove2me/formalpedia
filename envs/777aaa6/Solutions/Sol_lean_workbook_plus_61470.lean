-- Prove2me | solution 1 for lean_workbook_plus_61470
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:35:02.00088+00:00
-- url     : https://prove2.me/submissions/7f0e4783-22d0-4e0c-8deb-aaf46f43b7e1

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a : ℝ) (h : a * (2 * a ^ 2 - 1) = 0) :
    a ∈ ({-Real.sqrt 2 / 2, 0, Real.sqrt 2 / 2} : Finset ℝ) := by
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rcases mul_eq_zero.mp h with ha | ha
  · exact Or.inr (Or.inl ha)
  · have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hp : (a - Real.sqrt 2 / 2) * (a + Real.sqrt 2 / 2) = 0 := by nlinarith
    rcases mul_eq_zero.mp hp with hpos | hneg
    · right; right; linarith
    · left; linarith

#print axioms solution
