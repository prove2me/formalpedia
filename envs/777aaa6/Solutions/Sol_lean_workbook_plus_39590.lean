-- Prove2me | solution 1 for lean_workbook_plus_39590
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:41:28.601433+00:00
-- url     : https://prove2.me/submissions/3871d05d-0d9d-443a-b31b-6f9450f20942

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ)
  (h₀ : a + b + c = 6)
  (h₁ : a^2 + b^2 + c^2 = 40)
  (h₂ : a^3 + b^3 + c^3 = 200) :
  a^2 * (b + c) + b^2 * (a + c) + c^2 * (a + b) = 40 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
