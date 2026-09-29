-- Prove2me | solution 1 for lean_workbook_plus_61644
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:20:02.356943+00:00
-- url     : https://prove2.me/submissions/92cb9302-c859-437d-acb7-99e7d5c77f59

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ)
  (h₀ : y = x + 100)
  (h₁ : x + y = 110) :
  x = 5 ∧ y = 105 := by
  (intros; constructor <;> nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
