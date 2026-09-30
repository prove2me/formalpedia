-- Prove2me | solution 1 for lean_workbook_plus_55862
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:13:46.711758+00:00
-- url     : https://prove2.me/submissions/2930bcbb-01fd-49be-ab4d-d3fb2b3867c1

import Mathlib
set_option autoImplicit false

theorem solution : ∀ x y : ℝ, x + y = 1 ∧ x >= 0 ∧ y >= 0 → x ^ 2 + y ^ 2 + x ^ 2 * y ^ 2 >= 9 / 16   := by
  rintro x y ⟨hxy, hx, hy⟩
  have hs : x ^ 2 + y ^ 2 + 2 * x * y = 1 := by
    nlinarith [congrArg (fun t : ℝ => t ^ 2) hxy]
  have ht : x * y ≤ 1 / 4 := by nlinarith [sq_nonneg (x - y)]
  have hg : 0 ≤ (1 / 4 - x * y) * (7 / 4 - x * y) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith [hg]

#print axioms solution
