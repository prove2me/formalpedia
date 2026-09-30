-- Prove2me | solution 1 for lean_workbook_plus_17338
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:28:00.298086+00:00
-- url     : https://prove2.me/submissions/5f267343-f85b-48dd-b90f-00f08d639366

import Mathlib
set_option autoImplicit false

theorem solution (a b c : ℝ) : (a+b+c)^2 - 9*a*b >= 0 ∨ (a+b+c)^2 - 9*b*c >= 0 ∨ (a+b+c)^2 - 9*c*a >= 0   := by
  by_contra h
  push_neg at h
  nlinarith only [h.1, h.2.1, h.2.2, sq_nonneg (a - b),
    sq_nonneg (b - c), sq_nonneg (c - a)]

#print axioms solution
