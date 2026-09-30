-- Prove2me | solution 1 for lean_workbook_plus_7776
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:31:51.233909+00:00
-- url     : https://prove2.me/submissions/5b90e7b5-a46d-4aa6-aafd-ca129e47b279

import Mathlib

namespace PositiveSexticNoRoots

def value (x : ℝ) : ℝ := x ^ 6 + x ^ 5 + x ^ 4 - x ^ 3 - x ^ 2 + 1

theorem square_decomposition (x : ℝ) :
    value x = (x ^ 3 + x ^ 2 / 2 - 1 / 2) ^ 2 +
      (3 / 4 : ℝ) * (x ^ 2 - 1 / 3) ^ 2 + 2 / 3 := by
  unfold value
  ring

theorem lower_bound (x : ℝ) : 2 / 3 ≤ value x := by
  rw [square_decomposition]
  nlinarith [sq_nonneg (x ^ 3 + x ^ 2 / 2 - 1 / 2), sq_nonneg (x ^ 2 - 1 / 3)]

theorem strict_lower_bound (x : ℝ) : 2 / 3 < value x := by
  have h1 := sq_nonneg (x ^ 3 + x ^ 2 / 2 - 1 / 2)
  have h2 := sq_nonneg (x ^ 2 - 1 / 3)
  have hi := square_decomposition x
  by_contra h
  have he1 : (x ^ 3 + x ^ 2 / 2 - 1 / 2) ^ 2 = 0 := by nlinarith
  have he2 : (x ^ 2 - 1 / 3) ^ 2 = 0 := by nlinarith
  have hz1 := sq_eq_zero_iff.mp he1
  have hz2 := sq_eq_zero_iff.mp he2
  have hx2 : x ^ 2 = 1 / 3 := by linarith
  have hx3 : x ^ 3 = 1 / 3 := by linarith
  have hm := congrArg (fun t : ℝ => x * t) hx2
  have hx : x = 1 := by nlinarith only [hm, hx3]
  rw [hx] at hx2
  norm_num at hx2

theorem everywhere_positive (x : ℝ) : 0 < value x := by
  linarith [lower_bound x]

theorem no_real_zero : ¬ ∃ x : ℝ, value x = 0 := by
  rintro ⟨x, hx⟩
  exact (ne_of_gt (everywhere_positive x)) hx

end PositiveSexticNoRoots

theorem solution : ¬ ∃ x : ℝ, x ^ 6 + x ^ 5 + x ^ 4 - x ^ 3 - x ^ 2 + 1 = 0 := by
  exact PositiveSexticNoRoots.no_real_zero

#print axioms PositiveSexticNoRoots.square_decomposition
#print axioms PositiveSexticNoRoots.lower_bound
#print axioms PositiveSexticNoRoots.strict_lower_bound
#print axioms PositiveSexticNoRoots.everywhere_positive
#print axioms PositiveSexticNoRoots.no_real_zero
#print axioms solution
