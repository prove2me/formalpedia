-- Prove2me | solution 2 for lean_workbook_plus_8407
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:58:37.721925+00:00
-- url     : https://prove2.me/submissions/34a8b49a-5e5c-4e2e-8362-6c781ad225d4

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) : a ^ 2 + b ^ 2 ≥ a * b := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
