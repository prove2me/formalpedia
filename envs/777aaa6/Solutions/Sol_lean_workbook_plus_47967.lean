-- Prove2me | solution 1 for lean_workbook_plus_47967
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:18:23.438475+00:00
-- url     : https://prove2.me/submissions/077d921f-e154-4f76-afdf-ce883c2409fc

import Mathlib
set_option autoImplicit false

theorem solution (x y : ℝ) (h : x^4 + y^4 = 1) : -1 ≤ x ∧ x ≤ 1   := by
  have hx2 : x ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg (y ^ 2)]
  constructor <;> nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1)]

#print axioms solution
