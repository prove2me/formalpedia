-- Prove2me | solution 1 for lean_workbook_plus_37629
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:53:17.799273+00:00
-- url     : https://prove2.me/submissions/347cb8d0-932a-4237-b7a9-561ea3ca1fd4

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (hab : a * b > 0) : a + b ≠ 0 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
