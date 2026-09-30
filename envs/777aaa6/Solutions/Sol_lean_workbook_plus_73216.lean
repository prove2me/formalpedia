-- Prove2me | solution 1 for lean_workbook_plus_73216
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:49:31.256256+00:00
-- url     : https://prove2.me/submissions/9dffdca4-e73f-4730-be9f-25f13b614347

import Mathlib
set_option autoImplicit false

theorem solution (a b c : ℝ) : (a - b) ^ 2 + (a - c) ^ 2 ≥ 1 / 2 * (b - c) ^ 2   := by
  nlinarith only [sq_nonneg (a - (b + c) / 2)]

#print axioms solution
