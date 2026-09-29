-- Prove2me | solution 1 for lean_workbook_plus_66023
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:28:03.013355+00:00
-- url     : https://prove2.me/submissions/f2cc10e4-a10a-48f5-a261-3695e24e0656

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution : ∀ a b c : ℝ, 9 * (a ^ 2 + 3 * b ^ 2 + 5 * c ^ 2) ≥ (a + 3 * b + 5 * c) ^ 2 := by
  intro a b c
  nlinarith [sq_nonneg (a-b), sq_nonneg (a-c), sq_nonneg (b-c)]
