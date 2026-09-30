-- Prove2me | solution 1 for lean_workbook_plus_50411
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:12:38.308725+00:00
-- url     : https://prove2.me/submissions/a018b974-127e-4d94-ad11-9883c1f1e6be

import Mathlib
set_option autoImplicit false

theorem solution (a b c d : ℝ) : a + b + c + d = 4 → a * b + b * c + c * d + d * a ≤ 4   := by
  rintro h
  nlinarith [sq_nonneg (a - b + c - d)]

#print axioms solution
