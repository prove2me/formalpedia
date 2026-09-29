-- Prove2me | solution 1 for lean_workbook_plus_72640
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:20:55.16054+00:00
-- url     : https://prove2.me/submissions/eef54dd8-a58c-4936-b4b5-fe989fadf922

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : 2 * (a ^ 2 + b ^ 2 + c ^ 2) ≥ 2 * (a * b + b * c + c * a) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
