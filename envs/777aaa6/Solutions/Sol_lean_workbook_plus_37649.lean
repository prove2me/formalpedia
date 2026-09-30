-- Prove2me | solution 1 for lean_workbook_plus_37649
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:06:44.323153+00:00
-- url     : https://prove2.me/submissions/9437e31d-50ed-478c-8ccd-acc8139cc999

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

theorem positive_sum_product_remainder (a b : ℝ) :
    16 * ((a ^ 2 + b + 3 / 4) * (b ^ 2 + a + 3 / 4) - (a + b + 1 / 2) ^ 2) =
      (4 * a * b - 1) ^ 2 + 4 * (a + b - 1) ^ 2 * (a + b + 1) +
        12 * (a + b) * (a - b) ^ 2 := by
  ring

theorem positive_sum_product_bound (a b : ℝ) (hs : 0 ≤ a + b) :
    (a + b + 1 / 2) ^ 2 ≤ (a ^ 2 + b + 3 / 4) * (b ^ 2 + a + 3 / 4) := by
  have h1 := sq_nonneg (4 * a * b - 1)
  have h2 := mul_nonneg (sq_nonneg (a + b - 1))
    (show 0 ≤ a + b + 1 by linarith)
  have h3 := mul_nonneg hs (sq_nonneg (a - b))
  linarith [positive_sum_product_remainder a b]

theorem positive_sum_product_equality (a b : ℝ) (hs : 0 ≤ a + b) :
    (a ^ 2 + b + 3 / 4) * (b ^ 2 + a + 3 / 4) = (a + b + 1 / 2) ^ 2 ↔
      a = 1 / 2 ∧ b = 1 / 2 := by
  constructor
  · intro he
    have hp : 0 < a + b + 1 := by linarith
    have h1 := sq_nonneg (4 * a * b - 1)
    have h2 := mul_nonneg (sq_nonneg (a + b - 1)) hp.le
    have h3 := mul_nonneg hs (sq_nonneg (a - b))
    have hz1 : (4 * a * b - 1) ^ 2 = 0 := by
      linarith [positive_sum_product_remainder a b]
    have hz2 : (a + b - 1) ^ 2 * (a + b + 1) = 0 := by
      linarith [positive_sum_product_remainder a b]
    have hprod := sq_eq_zero_iff.mp hz1
    have hsum := sq_eq_zero_iff.mp ((mul_eq_zero.mp hz2).resolve_right hp.ne')
    have hd : a - b = 0 := by
      apply sq_eq_zero_iff.mp
      nlinarith [sq_nonneg (a - b)]
    constructor <;> linarith
  · rintro ⟨rfl, rfl⟩
    ring

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (a ^ 2 + b + 3 / 4) * (b ^ 2 + a + 3 / 4) ≥ (a + b + 1 / 2) ^ 2 :=
  positive_sum_product_bound a b (by linarith)

#print axioms solution
#print axioms positive_sum_product_equality
