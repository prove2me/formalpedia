-- Prove2me | solution 1 for lean_workbook_plus_34099
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:16:11.993677+00:00
-- url     : https://prove2.me/submissions/77721931-2f17-4cb9-89a7-0977110a8ca3

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : 8 * (a ^ 3 + b ^ 3 + c ^ 3) ≥ 3 * (a + b) * (b + c) * (c + a) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
