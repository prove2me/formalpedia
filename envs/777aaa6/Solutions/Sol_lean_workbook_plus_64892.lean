-- Prove2me | solution 1 for lean_workbook_plus_64892
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:07:06.112972+00:00
-- url     : https://prove2.me/submissions/4013f1f1-245d-4143-b2d4-0e466f3a7069

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) :
  14 * (a^2 + b^2 + c^2 - a * b - b * c - c * a)^2 + 9 * (a^2 + b^2 + c^2) * (a * b + b * c + c * a) ≥ 27 * a * b * c * (a + b + c) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
