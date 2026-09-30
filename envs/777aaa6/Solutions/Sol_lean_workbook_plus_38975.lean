-- Prove2me | solution 1 for lean_workbook_plus_38975
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:04:51.341405+00:00
-- url     : https://prove2.me/submissions/b60ada02-0c05-4ee5-8fea-c62cefbc25e8

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

theorem solution (m n : ℤ) (h : m ≠ n) (h2 : m ^ 2 + m * n + n ^ 2 = 1) :
    m ^ 3 - n ^ 3 = m - n := by
  calc
    m ^ 3 - n ^ 3 = (m - n) * (m ^ 2 + m * n + n ^ 2) := by ring
    _ = m - n := by rw [h2, mul_one]

#print axioms solution
