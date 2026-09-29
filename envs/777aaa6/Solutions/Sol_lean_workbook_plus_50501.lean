-- Prove2me | solution 1 for lean_workbook_plus_50501
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:20:26.746278+00:00
-- url     : https://prove2.me/submissions/157256d8-1544-4af3-9238-2fbaa70ef30c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) :
  a^4 + b^4 + c^4 ≥ a^3 * b + b^3 * c + c^3 * a := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
