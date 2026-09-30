-- Prove2me | solution 2 for lean_workbook_plus_73686
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:51:08.581053+00:00
-- url     : https://prove2.me/submissions/0ef03d4f-c2be-423f-b43c-bf8f3c674041

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (a^4 + b^4 + c^4) / 3 ≥ (a + b + c)^4 / 81 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
