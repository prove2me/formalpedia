-- Prove2me | solution 1 for lean_workbook_plus_24763
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:27:50.18735+00:00
-- url     : https://prove2.me/submissions/c52e6cf3-8159-496f-b138-13c175a2e317

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) :
  3 * (a ^ 2 + b ^ 2 + c ^ 2) + (a + b + c) ^ 2 ≥ 6 * (a * b + b * c + a * c) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
