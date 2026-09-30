-- Prove2me | solution 2 for lean_workbook_plus_44767
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:15:56.804822+00:00
-- url     : https://prove2.me/submissions/d98f6b2f-bbb3-4e88-b664-42eabc698b6e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ)
  (h₀ : 0 < a ∧ 0 < b)
  (h₁ : a * b = 4)
  (h₂ : a + b = 4) :
  a = 2 ∧ b = 2 := by
  (intros; constructor <;> nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
