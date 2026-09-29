-- Prove2me | solution 1 for lean_workbook_plus_10753
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:39:29.58347+00:00
-- url     : https://prove2.me/submissions/7c94a84d-92ab-4fa3-97e5-d2b9cf206db5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) : (d ^ 2 + b ^ 2) * (c ^ 2 + a ^ 2) ≥ (4 / 6561) * (8 * a + c) * (8 * b + d) * (8 * c + a) * (8 * d + b) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (d), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (a + d), sq_nonneg (b + c), sq_nonneg (b + d), sq_nonneg (c + d)])
