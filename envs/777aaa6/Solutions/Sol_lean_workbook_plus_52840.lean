-- Prove2me | solution 1 for lean_workbook_plus_52840
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:16:39.386717+00:00
-- url     : https://prove2.me/submissions/002786f6-657d-46d6-9a6a-5c12863a05ae

import Mathlib
set_option autoImplicit false

theorem solution (a : ℝ) (ha : 0 < a) : (a * (3 * a + 1)) / (a + 1) ^ 2 ≤ (3 / 4 : ℝ) * a + 1 / 4   := by
  have hd : 0 < (a + 1) ^ 2 := sq_pos_of_pos (by linarith)
  have hp : 0 ≤ (3 * a + 1) * (a - 1) ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg (a - 1))
  apply (div_le_iff₀ hd).2
  nlinarith only [hp]

#print axioms solution
