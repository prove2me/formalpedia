-- Prove2me | solution 1 for lean_workbook_plus_53610
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:46:18.683331+00:00
-- url     : https://prove2.me/submissions/98ebd4e4-ae20-40ce-99da-ba0d45c20a71

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (b c : ℝ) : (b^3 + c^3) * (b + c) ≤ 2 * (b^4 + c^4) := by
  (intros; nlinarith [sq_nonneg (b), sq_nonneg (c), sq_nonneg (b - c), sq_nonneg (b + c)])
