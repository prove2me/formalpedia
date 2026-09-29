-- Prove2me | solution 1 for lean_workbook_plus_76741
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:27:14.738675+00:00
-- url     : https://prove2.me/submissions/27ddbd95-e360-446a-b7f4-16a246e429e5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (h₁ : 0 ≤ a) (h₂ : 0 ≤ b) (h₃ : 2 * a + b ≤ 3) : -3 ≤ a - b + a * b ∧ a - b + a * b ≤ 3 / 2 := by
  (intros; constructor <;> nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
