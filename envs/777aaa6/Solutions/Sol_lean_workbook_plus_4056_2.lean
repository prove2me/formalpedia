-- Prove2me | solution 2 for lean_workbook_plus_4056
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:15:47.292041+00:00
-- url     : https://prove2.me/submissions/916727c9-3bb3-475d-b4db-075cdc57e2d8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 ≥ a ^ 2 * b * c + b ^ 2 * c * a + c ^ 2 * a * b := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
