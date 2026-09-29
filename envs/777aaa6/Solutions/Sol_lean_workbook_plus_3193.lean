-- Prove2me | solution 1 for lean_workbook_plus_3193
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:14:56.306384+00:00
-- url     : https://prove2.me/submissions/aa741caf-4092-4d7a-83d8-652e2b2d31bf

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) (h1 : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) (h2 : a ≤ b ∧ b ≤ c ∧ c ≤ d) : 7 * a ^ 2 + 5 * b ^ 2 + 3 * c ^ 2 + d ^ 2 ≤ (a + b + c + d) ^ 2 ∧ (a + b + c + d) ^ 2 ≤ a ^ 2 + 3 * b ^ 2 + 5 * c ^ 2 + 7 * d ^ 2 := by
  (intros; constructor <;> nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (d), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (a + d), sq_nonneg (b + c), sq_nonneg (b + d), sq_nonneg (c + d)])
