-- Prove2me | solution 1 for lean_workbook_plus_16830
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:22:07.002032+00:00
-- url     : https://prove2.me/submissions/f7d31016-8e38-4665-9889-52e7b9c482ec

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) : (a^2 - a * b + b^2)^2 ≥ 1/2 * (a^4 + b^4) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
