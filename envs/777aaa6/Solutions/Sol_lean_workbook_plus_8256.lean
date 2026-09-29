-- Prove2me | solution 1 for lean_workbook_plus_8256
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:49:50.65506+00:00
-- url     : https://prove2.me/submissions/dfdadd3d-465e-4fa0-95a1-4fe88f368b0c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) (h1 : a > b ∧ b > c ∧ c > d) : a * d + b * c < a * c + b * d ∧ a * c + b * d < a * b + c * d := by
  (intros; constructor <;> nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (d), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (a + d), sq_nonneg (b + c), sq_nonneg (b + d), sq_nonneg (c + d)])
