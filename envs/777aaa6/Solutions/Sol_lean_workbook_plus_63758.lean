-- Prove2me | solution 1 for lean_workbook_plus_63758
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:03:12.241542+00:00
-- url     : https://prove2.me/submissions/ed61363e-f23d-43ad-b34f-321ec9fd412a

import Mathlib
set_option autoImplicit false

theorem solution : (1 / 2 * (1 / Real.sqrt 3) + (1 / 3) / ((1 / 3) ^ 2 + 3)) < (3:ℝ) / 4   := by
  have hs : (1 : ℝ) ≤ Real.sqrt 3 := Real.le_sqrt_of_sq_le (by norm_num)
  have hp : 0 < Real.sqrt 3 := lt_of_lt_of_le zero_lt_one hs
  have hi : 1 / Real.sqrt 3 ≤ 1 := (div_le_iff₀ hp).2 (by simpa using hs)
  simp only [one_div] at hi
  norm_num at ⊢
  linarith

#print axioms solution
