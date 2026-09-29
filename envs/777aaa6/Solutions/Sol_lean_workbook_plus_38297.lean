-- Prove2me | solution 1 for lean_workbook_plus_38297
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:52:21.80681+00:00
-- url     : https://prove2.me/submissions/dfefd523-3ffd-44b3-bbd5-249c070c13ea

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : a^4 + b^4 + c^4 ≥ a^3 * b + b^3 * c + c^3 * a := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
