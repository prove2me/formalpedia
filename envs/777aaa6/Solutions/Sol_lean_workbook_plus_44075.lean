-- Prove2me | solution 1 for lean_workbook_plus_44075
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:28:33.035804+00:00
-- url     : https://prove2.me/submissions/792c0617-c3be-4d0a-bed3-283f28bba249

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (a + c) ^ 2 + 3 * b ^ 2 ≥ 3 * a * b + 3 * b * c + a * c := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
