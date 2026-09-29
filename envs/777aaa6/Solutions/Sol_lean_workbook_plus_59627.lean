-- Prove2me | solution 1 for lean_workbook_plus_59627
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:34:00.737285+00:00
-- url     : https://prove2.me/submissions/caa76fb7-4021-41a7-a430-81f535636021

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : a * (b + c) / 2 + b * (c + a) / 2 + c * (a + b) / 2 ≤ (a + b + c) ^ 2 / 3 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
