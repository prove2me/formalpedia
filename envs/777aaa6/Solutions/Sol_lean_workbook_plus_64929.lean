-- Prove2me | solution 1 for lean_workbook_plus_64929
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:34:38.22158+00:00
-- url     : https://prove2.me/submissions/1df2c5c0-ecae-4d9f-8e4e-4e485a9f79f4

import Mathlib

namespace TwelfthDegreePositivePolynomial

theorem quartic_identity (y : ℝ) :
    256 * (y ^ 4 - y ^ 3) + 27 = (4 * y - 3) ^ 2 * ((4 * y + 1) ^ 2 + 2) := by ring

theorem quartic_minimum (y : ℝ) :
    -(27 / 256 : ℝ) ≤ y ^ 4 - y ^ 3 ∧
      (y ^ 4 - y ^ 3 = -(27 / 256 : ℝ) ↔ y = 3 / 4) := by
  have h := quartic_identity y
  have hp : 0 < (4 * y + 1) ^ 2 + 2 := by positivity
  have hn := mul_nonneg (sq_nonneg (4 * y - 3)) (le_of_lt hp)
  constructor
  · nlinarith
  · constructor
    · intro he
      have hz : (4 * y - 3) ^ 2 * ((4 * y + 1) ^ 2 + 2) = 0 := by linarith
      have hh := (mul_eq_zero.mp hz).resolve_right (ne_of_gt hp)
      nlinarith [sq_nonneg (4 * y - 3)]
    · rintro rfl
      norm_num

theorem strict_two_squares (x : ℝ) :
    0 < (x ^ 2 - 1 / 2) ^ 2 + (x - 1 / 2) ^ 2 := by
  by_contra h
  have hle : (x ^ 2 - 1 / 2) ^ 2 + (x - 1 / 2) ^ 2 ≤ 0 := le_of_not_gt h
  have hx : x = 1 / 2 := by nlinarith [sq_nonneg (x ^ 2 - 1 / 2)]
  subst x
  norm_num at hle

theorem square_decomposition (x : ℝ) :
    256 * (x ^ 12 - x ^ 9 + x ^ 4 - x + 1 - 101 / 256) =
      (4 * x ^ 3 - 3) ^ 2 * ((4 * x ^ 3 + 1) ^ 2 + 2) +
        256 * ((x ^ 2 - 1 / 2) ^ 2 + (x - 1 / 2) ^ 2) := by ring

theorem uniform_bound (x : ℝ) : 101 / 256 < x ^ 12 - x ^ 9 + x ^ 4 - x + 1 := by
  have h := square_decomposition x
  have hp := strict_two_squares x
  have hn : 0 ≤ (4 * x ^ 3 - 3) ^ 2 * ((4 * x ^ 3 + 1) ^ 2 + 2) := by positivity
  linarith

theorem no_real_roots (x : ℝ) : x ^ 12 - x ^ 9 + x ^ 4 - x + 1 ≠ 0 := by
  have h := uniform_bound x
  linarith

end TwelfthDegreePositivePolynomial

theorem solution (x : ℝ) : x ^ 12 - x ^ 9 + x ^ 4 - x + 1 > 0 := by
  have h := TwelfthDegreePositivePolynomial.uniform_bound x
  linarith

#print axioms TwelfthDegreePositivePolynomial.quartic_identity
#print axioms TwelfthDegreePositivePolynomial.quartic_minimum
#print axioms TwelfthDegreePositivePolynomial.strict_two_squares
#print axioms TwelfthDegreePositivePolynomial.square_decomposition
#print axioms TwelfthDegreePositivePolynomial.uniform_bound
#print axioms TwelfthDegreePositivePolynomial.no_real_roots
#print axioms solution
