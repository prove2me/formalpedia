-- Prove2me | solution 1 for lean_workbook_plus_61613
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:55:43.544213+00:00
-- url     : https://prove2.me/submissions/b584879e-f088-4fa7-af87-a0e59837642f

import Mathlib
set_option autoImplicit false

theorem solution (a b c d e : ℝ) : a^2 - a * (b + c + d + e) + b^2 + c^2 + d^2 + e^2 ≥ 0   := by
  nlinarith [sq_nonneg (b - a / 2), sq_nonneg (c - a / 2),
    sq_nonneg (d - a / 2), sq_nonneg (e - a / 2)]

#print axioms solution
