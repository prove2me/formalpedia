-- Prove2me | solution 1 for lean_workbook_plus_51167
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:16:50.862839+00:00
-- url     : https://prove2.me/submissions/6aa7150e-28ec-4ef1-a7bf-f4c7a65c7bd6

import Mathlib
set_option autoImplicit false

theorem solution (x : ℝ) : (x - 1) * (x - 3) * (x - 4) * (x - 6) + 9 ≥ 0   := by
  have he : (x - 1) * (x - 3) * (x - 4) * (x - 6) + 9 = (x ^ 2 - 7 * x + 9) ^ 2 := by ring
  rw [he]
  exact sq_nonneg _

#print axioms solution
