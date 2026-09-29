-- Prove2me | solution 1 for lean_workbook_plus_46579
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:14:51.569145+00:00
-- url     : https://prove2.me/submissions/c7ce30bc-a835-4181-8a26-299957b0bd2b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : a * b + b * c + c * a = 3) :
  3 ≤ a + b + c := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
