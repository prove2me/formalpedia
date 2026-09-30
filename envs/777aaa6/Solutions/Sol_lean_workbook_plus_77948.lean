-- Prove2me | solution 1 for lean_workbook_plus_77948
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T02:10:19.969865+00:00
-- url     : https://prove2.me/submissions/a2221295-89ca-43ec-9b53-c41270bfcac5

import Mathlib.Analysis.Complex.Basic

theorem solution (x y : ℝ) (f : ℝ × ℝ → ℝ) (hf: f (x,y) = if (-x) ≤ y ∧ y ≤ x then y else if x ≤ y ∧ y ≤ (-x) then (-y) else if (-y) ≤ x ∧ x ≤ y then x else (-y)) : |f (x,y)| ≤ |x| + |y| := by
  rw [hf]
  have hx : 0 ≤ |x| := abs_nonneg x
  have hy : 0 ≤ |y| := abs_nonneg y
  have hny : |-y| = |y| := abs_neg y
  split_ifs <;> linarith
