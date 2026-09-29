-- Prove2me | solution 1 for lean_workbook_plus_1534
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:33:05.115395+00:00
-- url     : https://prove2.me/submissions/7ec81901-7a70-4b82-b03f-16006cb92c70

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : a + b + c = 3)
  (h₂ : a * b + b * c + c * a = 3) :
  a * b * c ≥ 1 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
