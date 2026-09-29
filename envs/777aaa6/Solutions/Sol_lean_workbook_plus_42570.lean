-- Prove2me | solution 1 for lean_workbook_plus_42570
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:17:03.513191+00:00
-- url     : https://prove2.me/submissions/446b74f4-51ee-4799-ae05-1bc3bcdea483

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (h : x > 3) : (x - 1) ^ 3 < x ^ 3 - x + 3 ∧ x ^ 3 - x + 3 < x ^ 3 := by
  (intros; constructor <;> nlinarith [sq_nonneg (x)])
