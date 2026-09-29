-- Prove2me | solution 1 for lean_workbook_plus_34606
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:43:10.517358+00:00
-- url     : https://prove2.me/submissions/be05cf4d-0bc3-4b26-b035-bc06a640465a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : 2 * (a ^ 4 + b ^ 4 + c ^ 4) ≥ a ^ 3 * b + a * b ^ 3 + a ^ 3 * c + a * c ^ 3 + b ^ 3 * c + b * c ^ 3 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
