-- Prove2me | solution 1 for lean_workbook_plus_43954
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:28:43.215643+00:00
-- url     : https://prove2.me/submissions/2318032d-cfb1-41b4-bb77-8ac3efdee5c9

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (h₁ : x + 2*y = 8) (h₂ : 3*x - y = 10) : x = 4 ∧ y = 2 := by
  (intros; constructor <;> nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
