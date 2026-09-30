-- Prove2me | solution 1 for lean_workbook_plus_78657
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:25:17.087816+00:00
-- url     : https://prove2.me/submissions/776a2c6c-a366-44a4-a059-5557bf40d646

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

private theorem pair_bound (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    1 / (x + y) ≤ (1 / x + 1 / y) / 4 := by
  have hsum : 0 < x + y := add_pos hx hy
  have hidentity :
      (1 / x + 1 / y) / 4 - 1 / (x + y) = (x - y) ^ 2 / (4 * x * y * (x + y)) := by
    field_simp [ne_of_gt hx, ne_of_gt hy, ne_of_gt hsum]
    <;> ring
  have : 0 ≤ (x - y) ^ 2 / (4 * x * y * (x + y)) := by positivity
  linarith

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    1 / (2 * a) + 1 / (2 * b) + 1 / (2 * c) ≥
      1 / (b + c) + 1 / (c + a) + 1 / (a + b) := by
  have hab := pair_bound a b ha hb
  have hbc := pair_bound b c hb hc
  have hca := pair_bound c a hc ha
  have ha2 : 1 / (2 * a) = (1 / a) / 2 := by field_simp
  have hb2 : 1 / (2 * b) = (1 / b) / 2 := by field_simp
  have hc2 : 1 / (2 * c) = (1 / c) / 2 := by field_simp
  rw [ha2, hb2, hc2]
  linarith

#print axioms solution
