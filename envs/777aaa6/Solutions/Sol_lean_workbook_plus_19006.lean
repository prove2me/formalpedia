-- Prove2me | solution 1 for lean_workbook_plus_19006
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:52:27.975224+00:00
-- url     : https://prove2.me/submissions/6b26b406-7553-4c23-9bbf-f33979be3bd2

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b c : ℂ) (h : a + b + c = 0) :
    2 * (a - b) ^ 2 * (b - c) ^ 2 * (c - a) ^ 2 =
      (a ^ 2 + b ^ 2 + c ^ 2) ^ 3 - 54 * a ^ 2 * b ^ 2 * c ^ 2 := by
  have hc : c = -(a + b) := by linear_combination h
  rw [hc]
  ring

#print axioms solution
