-- Prove2me | solution 1 for lean_workbook_plus_50698
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:16:53.530511+00:00
-- url     : https://prove2.me/submissions/ab4ac6d5-d056-46fd-9e8b-bc731cbfe340

import Mathlib
set_option autoImplicit false

theorem solution (a b c d x y : ℝ) : (a * x + b * y) ^ 2 + (c * x + d * y) ^ 2 ≤ (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * (x ^ 2 + y ^ 2)   := by
  ring_nf
  nlinarith [sq_nonneg (a * y - b * x), sq_nonneg (c * y - d * x)]

#print axioms solution
