-- Prove2me | solution 1 for lean_workbook_plus_40071
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:41:02.776212+00:00
-- url     : https://prove2.me/submissions/368603a6-7762-4f8d-840d-e7399f33e4c5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c x y : ℝ) : (a+b+c)*(a^2+b^2+c^2-a*b-b*c-c*a) = a^3+b^3+c^3-3*a*b*c ∧ (x+y)*(x^2-x*y+y^2) = x^3+y^3 := by
  (intros; constructor <;> nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (x), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - x), sq_nonneg (b - c), sq_nonneg (b - x), sq_nonneg (c - x), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (a + x), sq_nonneg (b + c), sq_nonneg (b + x), sq_nonneg (c + x)])
