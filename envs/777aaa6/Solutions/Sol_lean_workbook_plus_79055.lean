-- Prove2me | solution 1 for lean_workbook_plus_79055
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:37:35.967896+00:00
-- url     : https://prove2.me/submissions/d691428d-81d4-406b-b6f0-e4787dcffb8b

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution : ∀ x y : ℝ, Real.sqrt ((x + 2) ^ 2 + (y + 2) ^ 2) ≥
    (x + 2 + y + 2) / Real.sqrt 2 := by
  intro x y
  apply Real.le_sqrt_of_sq_le
  rw [div_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  nlinarith [sq_nonneg (x - y)]

#print axioms solution
