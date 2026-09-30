-- Prove2me | solution 1 for lean_workbook_plus_57203
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:12:30.316481+00:00
-- url     : https://prove2.me/submissions/4da4c5a3-5b40-4ad2-a584-3666061245c1

import Mathlib
set_option autoImplicit false

theorem solution : ∀ a b : ℝ, a^2 * (1 + b^4) + b^2 * (1 + a^4) ≤ (1 + a^4) * (1 + b^4)   := by
  intro a b
  have ha4 : 0 ≤ 1 + a ^ 4 := by positivity
  have hb4 : 0 ≤ 1 + b ^ 4 := by positivity
  have h1 := mul_nonneg (sq_nonneg (a ^ 2 - 1)) hb4
  have h2 := mul_nonneg (sq_nonneg (b ^ 2 - 1)) ha4
  nlinarith only [h1, h2]

#print axioms solution
