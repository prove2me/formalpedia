-- Prove2me | solution 1 for lean_workbook_plus_23917
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:16:11.050829+00:00
-- url     : https://prove2.me/submissions/30277989-40a8-4b56-b63f-f44094fb1fc1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ)
  (h₀ : a + b + c = 2) :
  1 / 3 * (a + b + c)^2 ≥ a * b + b * c + c * a → a * b + b * c + c * a ≤ 4 / 3 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
