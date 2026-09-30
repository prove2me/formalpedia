-- Prove2me | solution 1 for lean_workbook_plus_78620
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:38:05.586604+00:00
-- url     : https://prove2.me/submissions/5cd2140c-baf9-4fd9-8f29-cbf2526d8af2

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

theorem solution (a : ℝ) : a + a ^ 3 - a ^ 4 - a ^ 6 < 3 / 4 := by
  by_contra h
  have h0 := sq_nonneg (a - 1 / 2)
  have h1 := sq_nonneg (a ^ 2 - 1 / 2)
  have h2 := sq_nonneg (a ^ 3 - 1 / 2)
  have hz : (a - 1 / 2) ^ 2 = 0 := by nlinarith
  have ha : a = 1 / 2 := sub_eq_zero.mp (sq_eq_zero_iff.mp hz)
  subst a
  norm_num at h

#print axioms solution
