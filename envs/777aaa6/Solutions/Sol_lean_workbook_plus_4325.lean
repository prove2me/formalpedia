-- Prove2me | solution 1 for lean_workbook_plus_4325
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:28:07.496652+00:00
-- url     : https://prove2.me/submissions/5b727c7a-14de-4257-9c34-88c3bb89dfe8

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

private theorem strip_square_bounds (u v : ℝ) (hu : |u| ≤ 3) (hv : |v| ≤ 1) :
    0 ≤ 9 - u ^ 2 ∧ 0 ≤ 1 - v ^ 2 ∧ 0 ≤ 3 + u * v := by
  obtain ⟨hu0, hu1⟩ := abs_le.mp hu
  obtain ⟨hv0, hv1⟩ := abs_le.mp hv
  have h1 := mul_nonneg (show 0 ≤ 3 - u by linarith) (show 0 ≤ 3 + u by linarith)
  have h2 := mul_nonneg (show 0 ≤ 1 - v by linarith) (show 0 ≤ 1 + v by linarith)
  have h3 := mul_nonneg (show 0 ≤ 3 - u by linarith) (show 0 ≤ 1 - v by linarith)
  have h4 := mul_nonneg (show 0 ≤ 3 + u by linarith) (show 0 ≤ 1 + v by linarith)
  exact ⟨by nlinarith, by nlinarith, by nlinarith⟩

theorem strip_quadratic_gap_identity (x y : ℝ) :
    175 - 25 * (x ^ 2 + x * y + y ^ 2) =
      13 * (9 - (2 * x - y) ^ 2) + 7 * (1 - (x - 3 * y) ^ 2) +
        17 * (3 + (2 * x - y) * (x - 3 * y)) := by ring

theorem strip_quadratic_sharp_bound (x y : ℝ)
    (h1 : |2 * x - y| ≤ 3) (h2 : |x - 3 * y| ≤ 1) :
    x ^ 2 + x * y + y ^ 2 ≤ 7 := by
  obtain ⟨ha, hb, hc⟩ := strip_square_bounds _ _ h1 h2
  nlinarith [strip_quadratic_gap_identity x y]

theorem strip_quadratic_equality (x y : ℝ)
    (h1 : |2 * x - y| ≤ 3) (h2 : |x - 3 * y| ≤ 1) :
    x ^ 2 + x * y + y ^ 2 = 7 ↔
      (x = 2 ∧ y = 1) ∨ (x = -2 ∧ y = -1) := by
  constructor
  · intro h
    obtain ⟨ha, hb, hc⟩ := strip_square_bounds _ _ h1 h2
    have hu : (2 * x - y) ^ 2 = 9 := by
      nlinarith [strip_quadratic_gap_identity x y]
    have huv : (2 * x - y) * (x - 3 * y) = -3 := by
      nlinarith [strip_quadratic_gap_identity x y]
    have hf : (2 * x - y - 3) * (2 * x - y + 3) = 0 := by nlinarith
    rcases mul_eq_zero.mp hf with hp | hm
    · left
      constructor <;> nlinarith
    · right
      constructor <;> nlinarith
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> ring

theorem strip_quadratic_attained :
    |2 * (2 : ℝ) - 1| ≤ 3 ∧ |(2 : ℝ) - 3 * 1| ≤ 1 ∧
      (2 : ℝ) ^ 2 + 2 * 1 + 1 ^ 2 = 7 := by norm_num

theorem solution (x y : ℝ) (h1 : abs (2*x - y) ≤ 3) (h2 : abs (x - 3*y) ≤ 1) :
    x^2 + x*y + y^2 ≤ 7 := strip_quadratic_sharp_bound x y h1 h2

#print axioms solution
#print axioms strip_quadratic_gap_identity
#print axioms strip_quadratic_sharp_bound
#print axioms strip_quadratic_equality
#print axioms strip_quadratic_attained
