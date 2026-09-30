-- Prove2me | solution 1 for lean_workbook_plus_29255
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:42:07.358713+00:00
-- url     : https://prove2.me/submissions/b7f56ce6-e0a1-4710-8b1c-014aca5dbdba

import Mathlib
set_option autoImplicit false

theorem solution (x1 x2 x3 : ℝ) (hx1 : 0 < x1) (hx2 : 0 < x2) (hx3 : 0 < x3) (hx : x1 + x2 + x3 = 1) : x1 * x2 + x1 * x3 + x2 * x3 ≤ 1 / 3   := by
  have hs : (x1 + x2 + x3) ^ 2 = 1 := by rw [hx]; norm_num
  nlinarith only [hs, sq_nonneg (x1 - x2), sq_nonneg (x1 - x3), sq_nonneg (x2 - x3)]

#print axioms solution
