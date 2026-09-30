-- Prove2me | solution 2 for lean_workbook_plus_79750
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:59:51.548024+00:00
-- url     : https://prove2.me/submissions/7978d8d1-de4d-422c-a042-e9dc6eb3751a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : a^4 + b^4 + c^4 ≥ a * b * c * (a + b + c) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
