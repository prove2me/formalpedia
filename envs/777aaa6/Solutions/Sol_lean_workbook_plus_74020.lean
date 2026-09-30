-- Prove2me | solution 1 for lean_workbook_plus_74020
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:39:22.621594+00:00
-- url     : https://prove2.me/submissions/5c6a72d1-c0e7-473b-b643-d9cffb31363e

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

theorem solution (a b c : ℂ) (h : a+b+c = 0) :
    2*(a^5+b^5+c^5) = 5*a*b*c*(a^2+b^2+c^2) := by
  have hc : c = -(a+b) := eq_neg_of_add_eq_zero_right h
  rw [hc]
  ring
