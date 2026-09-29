-- Prove2me | solution 1 for lean_workbook_plus_45444
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:49:57.876341+00:00
-- url     : https://prove2.me/submissions/df6ba0cf-4bd9-4f08-9f5f-ff1741c6e6df

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (h : x + y + z ≥ x * y * z) : x^2 + y^2 + z^2 ≥ x * y * z := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
