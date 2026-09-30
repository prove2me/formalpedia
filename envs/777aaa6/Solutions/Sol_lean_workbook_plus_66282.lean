-- Prove2me | solution 1 for lean_workbook_plus_66282
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:58:40.450063+00:00
-- url     : https://prove2.me/submissions/e312376b-9b84-485f-84c5-bcc7438b4c90

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : 2 * x + y ^ 2 = y ^ 3 + y + 1) :
    2 * y + x ^ 2 ≤ x ^ 3 + x + 1 := by
  have hxy : y ≤ x := by
    nlinarith [mul_nonneg (sq_nonneg (y - 1)) (by linarith : 0 ≤ y + 1)]
  nlinarith [mul_nonneg (sq_nonneg (x - 1)) (by linarith : 0 ≤ x + 1)]

theorem equality_case (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : 2 * x + y ^ 2 = y ^ 3 + y + 1) :
    2 * y + x ^ 2 = x ^ 3 + x + 1 ↔ x = 1 ∧ y = 1 := by
  constructor
  · intro heq
    have hx1 := sq_nonneg (x - 1)
    have hy1 := sq_nonneg (y - 1)
    have hyx : y ≤ x := by
      nlinarith [mul_nonneg hy1 (by linarith : 0 ≤ y + 1)]
    have hxy : x ≤ y := by
      nlinarith [mul_nonneg hx1 (by linarith : 0 ≤ x + 1)]
    have he : x = y := le_antisymm hxy hyx
    have hp : (x - 1) ^ 2 * (x + 1) = 0 := by rw [← he] at h; nlinarith [h]
    have hs : (x - 1) ^ 2 = 0 := (mul_eq_zero.mp hp).resolve_right (by linarith)
    have hxone : x = 1 := by nlinarith [hs]
    exact ⟨hxone, he.symm.trans hxone⟩
  · rintro ⟨rfl, rfl⟩
    norm_num

#print axioms solution
#print axioms equality_case
