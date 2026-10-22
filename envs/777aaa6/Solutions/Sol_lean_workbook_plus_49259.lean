-- Prove2me | solution 1 for lean_workbook_plus_49259
-- status  : ACCEPTED   (prove)
-- author  : @Yivy Yu
-- created : 2026-04-15T02:20:08.452367+00:00
-- url     : https://prove2.me/submissions/ac808077-9bd4-4f88-ab76-5338c2d67408

import Theorems.Thm_lean_workbook_plus_49259

theorem solution (a b x y : ℝ) (h₁ : a + b = x) (h₂ : a * b = y) (h₃ : a^2 + b^2 = a + b) : x^2 - 2*y = x := by
  nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg (a + b)]
