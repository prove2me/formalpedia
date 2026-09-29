-- Prove2me | solution 1 for lean_workbook_plus_27287
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:14:47.865258+00:00
-- url     : https://prove2.me/submissions/d77f1686-ea77-4447-bf19-b5215313334b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℝ) (h1 : 1 / 2 < a) (h2 : a < 1) : 5 * a - 2 * a ^ 2 - 2 < 1 := by
  (intros; nlinarith [sq_nonneg (a)])
