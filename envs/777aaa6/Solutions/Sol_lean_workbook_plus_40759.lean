-- Prove2me | solution 1 for lean_workbook_plus_40759
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:39:54.950904+00:00
-- url     : https://prove2.me/submissions/54f9aa47-40ee-4ea7-ac65-16e3dec6e678

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (a + b) ^ 2 * (a + c) ^ 2 ≥ 4 * a * (b + c) * (a ^ 2 + b * c) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
