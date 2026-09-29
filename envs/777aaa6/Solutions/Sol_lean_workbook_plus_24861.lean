-- Prove2me | solution 1 for lean_workbook_plus_24861
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:27:40.115743+00:00
-- url     : https://prove2.me/submissions/7569b5af-4a7d-461d-b42e-c7ea6779717c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (h : x * y < 0) : x ^ 4 + y ^ 4 > x * y * (x ^ 2 + y ^ 2) := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
