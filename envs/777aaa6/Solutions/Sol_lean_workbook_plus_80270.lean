-- Prove2me | solution 1 for lean_workbook_plus_80270
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:33:21.74158+00:00
-- url     : https://prove2.me/submissions/c4ba9dd9-c36d-4536-9fb1-0cea749cbf56

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    7 * (a + b + c) * (a * b + b * c + c * a) ≤
      9 * a * b * c + 2 * (a + b + c) ^ 3 := by
  have hab := mul_nonneg (sq_nonneg (a - b)) (add_pos ha hb).le
  have hbc := mul_nonneg (sq_nonneg (b - c)) (add_pos hb hc).le
  have hca := mul_nonneg (sq_nonneg (c - a)) (add_pos hc ha).le
  nlinarith

#print axioms solution
