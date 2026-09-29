-- Prove2me | solution 1 for lean_workbook_plus_29319
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:18:26.320375+00:00
-- url     : https://prove2.me/submissions/44e4006e-8ee7-42db-9d5e-f5062b045f09

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y A B : ℂ) (h₁ : A = 1 - x) (h₂ : B = y) (h₃ : x^2 + x*y + y^2 - 2*x - y = 0) : A = 1 - x ∧ B = y ∧ x^2 + x*y + y^2 - 2*x - y = 0 := by
  (intros; simp_all)
