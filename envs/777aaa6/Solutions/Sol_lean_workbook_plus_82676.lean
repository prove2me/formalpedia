-- Prove2me | solution 1 for lean_workbook_plus_82676
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:35:15.369285+00:00
-- url     : https://prove2.me/submissions/1af7cbe3-6598-4e23-9baa-c172ea62ae79

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) : (a^4 / 2 + 3 * a^2 * b^2 + b^4 / 2) ≥ 2 * a * b * (a^2 + b^2) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
