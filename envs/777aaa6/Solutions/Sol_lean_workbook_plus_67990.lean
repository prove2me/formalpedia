-- Prove2me | solution 1 for lean_workbook_plus_67990
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:49:06.912954+00:00
-- url     : https://prove2.me/submissions/9fcb6e65-2d82-4e0a-9ef9-416fe6a506d7

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

theorem solution (a b c : ℝ) :
    a ^ 2 * b ^ 2 + a ^ 2 * c ^ 2 + b ^ 2 * c ^ 2 ≥
      a ^ 2 * b * c + a * b ^ 2 * c + a * b * c ^ 2 := by
  nlinarith [sq_nonneg (a * b - a * c), sq_nonneg (a * c - b * c),
    sq_nonneg (b * c - a * b)]

#print axioms solution
