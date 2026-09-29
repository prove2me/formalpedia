-- Prove2me | solution 1 for lean_workbook_plus_37647
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:53:15.345581+00:00
-- url     : https://prove2.me/submissions/154f8fb2-3088-442e-bcfd-ca676516fcdc

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (a * b + b * c + c * a) ^ 2 ≥ 3 * a * b * c * (a + b + c) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
