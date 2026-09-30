-- Prove2me | solution 1 for lean_workbook_plus_54511
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:44:21.170153+00:00
-- url     : https://prove2.me/submissions/866c7b47-f89c-44e1-87e0-014e1368ebcb

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b c x : ℝ) (ha : a ≠ 0) (h : b ^ 2 - 4 * a * c ≥ 0) :
    a * x ^ 2 + b * x + c =
      a * (x - (-b + Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a)) *
        (x - (-b - Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a)) := by
  have hs := Real.sq_sqrt h
  have he : b ^ 2 - a * c * 4 = b ^ 2 - 4 * a * c := by ring
  field_simp [ha]
  rw [he]
  linear_combination hs

#print axioms solution
