-- Prove2me | solution 1 for lean_workbook_plus_71316
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:52:06.190615+00:00
-- url     : https://prove2.me/submissions/49098e18-7757-401b-8a04-3823ee86240e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) :
  (a + b + c)^3 ≥ 27 * a * b * c := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
