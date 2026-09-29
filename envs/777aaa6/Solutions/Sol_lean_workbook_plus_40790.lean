-- Prove2me | solution 1 for lean_workbook_plus_40790
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:39:47.609882+00:00
-- url     : https://prove2.me/submissions/368adef7-e2ce-4a14-8622-61d9ab32851d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c: ℝ) : (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 >= 3 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
