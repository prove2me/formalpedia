-- Prove2me | solution 1 for lean_workbook_plus_77100
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:35:46.786673+00:00
-- url     : https://prove2.me/submissions/108138c6-3e1c-437f-ad5d-e35504ced176

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.LinearCombination

theorem solution (a b c : ℂ) (h : a + b + c = 0) :
    2 * (a^4 + b^4 + c^4) = (a^2 + b^2 + c^2)^2 := by
  have hc : c = -(a+b) := eq_neg_of_add_eq_zero_right h
  rw [hc]
  ring
