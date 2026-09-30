-- Prove2me | solution 2 for lean_workbook_plus_42969
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:16:34.950563+00:00
-- url     : https://prove2.me/submissions/00cf0c65-5ff3-47aa-b026-f28b451d98df

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : a^4 + b^4 + c^4 + a^2 * b^2 + b^2 * c^2 + c^2 * a^2 - 2 * a^3 * b - 2 * b^3 * c - 2 * c^3 * a ≥ 0 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
