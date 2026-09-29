-- Prove2me | solution 1 for lean_workbook_plus_59899
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:33:30.684765+00:00
-- url     : https://prove2.me/submissions/1238d198-18cd-42f0-9235-ddf13c0d8fef

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (hab : a ≥ b) (hbc : b ≥ c) (hca : c ≥ a) : a^4 + b^4 + c^4 ≥ a^3 * b + b^3 * c + c^3 * a := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
