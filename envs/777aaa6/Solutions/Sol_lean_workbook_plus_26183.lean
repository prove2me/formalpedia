-- Prove2me | solution 1 for lean_workbook_plus_26183
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:26:18.420805+00:00
-- url     : https://prove2.me/submissions/366b990d-4d0c-431d-a079-b618602e8b4c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (h : x > 1) : 2 * x ^ 2 + 8 * x + 6 > (x + 3) ^ 2 := by
  (intros; nlinarith [sq_nonneg (x)])
