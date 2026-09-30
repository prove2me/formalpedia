-- Prove2me | solution 1 for lean_workbook_plus_49431
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:01:01.362932+00:00
-- url     : https://prove2.me/submissions/9d26c76d-1bdb-4001-8fc3-2ae0d46a48cf

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

private theorem gap_identity (x y : ℝ) :
    4 * (x ^ 2 + y ^ 2) ^ 2 - y ^ 2 * (7 * x ^ 2 + 3 * x * y + 3 * y ^ 2) =
      (2 * x - y) ^ 2 * (x ^ 2 + x * y + y ^ 2) := by ring

theorem solution (x y : ℝ) (hy : 0 < y) :
    4 * (x ^ 2 + y ^ 2) ^ 2 ≥ y ^ 2 * (7 * x ^ 2 + 3 * x * y + 3 * y ^ 2) := by
  have hquad : 0 ≤ x ^ 2 + x * y + y ^ 2 := by
    nlinarith [sq_nonneg (x + y), sq_nonneg x, sq_nonneg y]
  have hp := mul_nonneg (sq_nonneg (2 * x - y)) hquad
  rw [← gap_identity] at hp
  linarith

theorem equality_case (x y : ℝ) (hy : 0 < y) :
    4 * (x ^ 2 + y ^ 2) ^ 2 = y ^ 2 * (7 * x ^ 2 + 3 * x * y + 3 * y ^ 2) ↔
      2 * x = y := by
  have hquad : 0 < x ^ 2 + x * y + y ^ 2 := by
    nlinarith [sq_nonneg (2 * x + y), sq_pos_of_pos hy]
  constructor
  · intro h
    have hp : (2 * x - y) ^ 2 * (x ^ 2 + x * y + y ^ 2) = 0 := by
      rw [← gap_identity, h, sub_self]
    have hs := (mul_eq_zero.mp hp).resolve_right (ne_of_gt hquad)
    nlinarith [hs]
  · intro h
    have hg := gap_identity x y
    rw [h, sub_self, zero_pow (by decide), zero_mul] at hg
    linarith

#print axioms solution
#print axioms equality_case
