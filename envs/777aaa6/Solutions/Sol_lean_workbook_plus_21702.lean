-- Prove2me | solution 1 for lean_workbook_plus_21702
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:45:42.672312+00:00
-- url     : https://prove2.me/submissions/75bd6a2a-1ce2-42d5-b746-16542ea3ec47

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : a^3 + b^3 + c^3 = (a + b + c)^3) : a^5 + b^5 + c^5 = (a + b + c)^5 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
