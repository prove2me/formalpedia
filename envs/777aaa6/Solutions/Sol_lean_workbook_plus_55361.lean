-- Prove2me | solution 1 for lean_workbook_plus_55361
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:02:02.821773+00:00
-- url     : https://prove2.me/submissions/5f6ab1ba-ff6d-4f37-a7fd-1726dc825316

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

theorem quadratic_product_remainder (a b c : ℝ) :
    6 * ((a ^ 2 + a * b + b ^ 2) * (b ^ 2 + b * c + c ^ 2) *
        (c ^ 2 + c * a + a ^ 2)) -
      2 * (a * b + b * c + c * a) ^ 2 *
        (2 * a ^ 2 + 2 * b ^ 2 + 2 * c ^ 2 + a * b + b * c + c * a) =
      (a + b + c) ^ 2 *
        ((a * b - b * c) ^ 2 + (b * c - c * a) ^ 2 + (c * a - a * b) ^ 2) := by
  ring

theorem quadratic_product_equality (a b c : ℝ) :
    (a + b + c) ^ 2 *
      ((a * b - b * c) ^ 2 + (b * c - c * a) ^ 2 + (c * a - a * b) ^ 2) = 0 ↔
    a + b + c = 0 ∨ (a * b = b * c ∧ b * c = c * a) := by
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (sq_eq_zero_iff.mp h)
    · right
      have h1 : (a * b - b * c) ^ 2 = 0 := by
        linarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a),
          sq_nonneg (c * a - a * b)]
      have h2 : (b * c - c * a) ^ 2 = 0 := by
        linarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a),
          sq_nonneg (c * a - a * b)]
      exact ⟨sub_eq_zero.mp (sq_eq_zero_iff.mp h1), sub_eq_zero.mp (sq_eq_zero_iff.mp h2)⟩
  · rintro (h | ⟨h1, h2⟩)
    · rw [h]
      ring
    · rw [h1, h2]
      ring

theorem solution (a b c : ℝ) :
    (a ^ 2 + a * b + b ^ 2) * (b ^ 2 + b * c + c ^ 2) *
      (c ^ 2 + c * a + a ^ 2) ≥
    1 / 3 * (a * b + b * c + c * a) ^ 2 *
      (2 * a ^ 2 + 2 * b ^ 2 + 2 * c ^ 2 + a * b + b * c + c * a) := by
  have hsq : 0 ≤ (a * b - b * c) ^ 2 + (b * c - c * a) ^ 2 +
      (c * a - a * b) ^ 2 :=
    add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)
  have h := mul_nonneg (sq_nonneg (a + b + c)) hsq
  linarith [quadratic_product_remainder a b c]

#print axioms solution
#print axioms quadratic_product_equality
