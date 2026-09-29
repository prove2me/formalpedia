-- Prove2me | solution 1 for lean_workbook_plus_53226
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:46:39.112299+00:00
-- url     : https://prove2.me/submissions/f9199fff-9285-4bac-b3a1-34970d83d500

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ)
  (h₀ : a * b * c = 1)
  (h₁ : a^2 + b^2 + c^2 - a * b - b * c - c * a = 0) :
  a^4 + b^2 * c^2 - 2 * a^2 * b * c = b^2 * c^2 + a^2 * b * c - a * b^3 - a * c^3 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
