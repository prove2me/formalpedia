-- Prove2me | solution 1 for lean_workbook_plus_50102
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:21:04.788033+00:00
-- url     : https://prove2.me/submissions/cefcbc8a-9463-4a95-854b-2875f39582d5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (h₁ : x + y = 2) (h₂ : x^2 + y^2 = 1) : x^3 + y^3 = 2 ∧ x^4 + y^4 = 2 ∧ x^5 + y^5 = 2 ∧ x^6 + y^6 = 2 ∧ x^30 + y^30 = 2 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
