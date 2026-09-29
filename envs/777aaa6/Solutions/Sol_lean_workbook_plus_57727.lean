-- Prove2me | solution 1 for lean_workbook_plus_57727
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:45:49.949906+00:00
-- url     : https://prove2.me/submissions/3718f93b-a6c9-45e6-8282-1ac79ae4aa0c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d e: ℝ) (h1 : 4 ≤ b + c + d + e ∧ b + c + d + e ≤ 44 / 5) (h2 : a + b + c + d + e = 8)  : -4 / 5 ≤ a ∧ a ≤ 4 := by
  (intros; constructor <;> nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (d), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (a + d), sq_nonneg (b + c), sq_nonneg (b + d), sq_nonneg (c + d)])
