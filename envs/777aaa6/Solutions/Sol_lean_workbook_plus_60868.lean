-- Prove2me | solution 1 for lean_workbook_plus_60868
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:32:39.987621+00:00
-- url     : https://prove2.me/submissions/99ac0e95-ea84-4c05-898f-941e62a127a5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (h₁ : x + y = 2) (h₂ : 2*x + y = 5) (h₃ : x - y = 4) : x = 3 ∧ y = -1 := by
  (intros; constructor <;> nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
