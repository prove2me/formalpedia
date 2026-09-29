-- Prove2me | solution 1 for lean_workbook_plus_41364
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:39:22.332133+00:00
-- url     : https://prove2.me/submissions/df744c5f-4850-4f36-8157-174ec50e9668

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) : 2 * (a ^ 4 + a ^ 2 * b ^ 2 + b ^ 4) ≥ 3 * (a ^ 3 * b + a * b ^ 3) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
