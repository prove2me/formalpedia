-- Prove2me | solution 2 for lean_workbook_plus_27941
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:06:03.900207+00:00
-- url     : https://prove2.me/submissions/e42aad69-d338-4698-93b8-223a741ba93f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : x ^ 4 + y ^ 4 + z ^ 4 ≥ (x + y + z) ^ 4 / 27 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
