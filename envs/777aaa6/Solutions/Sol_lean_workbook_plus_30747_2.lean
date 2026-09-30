-- Prove2me | solution 2 for lean_workbook_plus_30747
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:54:44.098472+00:00
-- url     : https://prove2.me/submissions/ff786dc0-ab82-429b-a8d3-3558fc39963c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ)
  (h₀ : a^2 + b^2 + c^2 = a * b + b * c + c * a)
  (h₁ : (c - a)^3 - (a - b)^3 = 0) :
  a = b ∧ b = c := by
  (intros; constructor <;> nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
