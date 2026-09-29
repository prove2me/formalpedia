-- Prove2me | solution 1 for lean_workbook_plus_16622
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:21:27.894637+00:00
-- url     : https://prove2.me/submissions/053871bf-4b69-4639-89f9-a802c129a9a2

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (a + b + c) ^ 2 ≥ 3 * (a * b + b * c + a * c) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
