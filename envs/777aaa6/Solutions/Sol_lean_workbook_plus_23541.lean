-- Prove2me | solution 1 for lean_workbook_plus_23541
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:55:16.14165+00:00
-- url     : https://prove2.me/submissions/295ada9e-147c-4e6f-a986-407d8946f5b1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : 8 * (a^2 + b^2 + c^2)^2 ≥ 3 * (2 * (a * b^3 + b * c^3 + c * a^3) + a^3 * b + b^3 * c + c^3 * a + 3 * a * b * c * (a + b + c)) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
