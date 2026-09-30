-- Prove2me | solution 1 for lean_workbook_plus_77129
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:05:30.035303+00:00
-- url     : https://prove2.me/submissions/7d52b91e-e812-41b7-973f-0e9e956be8cf

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

theorem solution (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=4) :
    a+a*b ≤ 25/4 := by
  have hbval : b = 4 - a := by linarith
  rw [hbval]
  nlinarith [sq_nonneg (a - 5/2)]
