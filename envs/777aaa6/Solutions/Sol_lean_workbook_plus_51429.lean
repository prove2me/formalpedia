-- Prove2me | solution 1 for lean_workbook_plus_51429
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:16:43.752921+00:00
-- url     : https://prove2.me/submissions/6d852f7b-2baa-4872-97c5-d8f7e304b4c9

import Mathlib
set_option autoImplicit false

theorem solution (x : ℝ) : x ^ 4 + x ^ 3 + 10 * x ^ 2 - 4 * x + 24 > 0   := by
  nlinarith only [sq_nonneg (x ^ 2 + x / 2), sq_nonneg (3 * x - 2 / 3), sq_nonneg x]

#print axioms solution
