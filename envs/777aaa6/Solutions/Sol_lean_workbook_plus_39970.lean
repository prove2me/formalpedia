-- Prove2me | solution 1 for lean_workbook_plus_39970
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:41:57.953076+00:00
-- url     : https://prove2.me/submissions/7e292bcc-2f60-4751-92aa-7cd89b510df4

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (h : x^3 + y^3 = 2) : x + y ≤ 2 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
